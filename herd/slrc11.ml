open Printf

module type Cfg = sig
  include Model.Config
end

module Make (*O:Model.Config*)(*S:Sem.Semantics*)(*SU:SlUtils.S*)(M:Mem.S)
  =
  struct
    module S = M.S
    module E = S.E
    module A = S.A
    module U = MemUtils.Make(S)
    module Sol = E.Act.A.V.Solution
  (*  module MU = ModelUtils.Make(O)(S)*)

    type exec = {
        po : E.EventRel.t;
        mo : E.EventRel.t;
        rf : E.EventRel.t;
        toadd : (int * E.EventSet.t) list;
        added : E.EventSet.t;
        revisit : E.EventSet.t;
        rmws : E.EventRel.t;
        exvals : E.event -> bool;
        rfm : M.S.rfmap;
        flags : Flag.Set.t;
        log : (string * exec) list;
        psc : E.EventRel.t;
        debug_rels : (string * E.EventRel.t) list;
      }

              (* debug *)

    let debug = true

    let debug_proc chan p = fprintf chan "%i" p

    let debug_event chan e = fprintf chan "%s:%s " (E.pp_eiid e) (S.E.Act.pp_action e.E.action)

    let debug_event_set chan e =
      let _ = print_string "[" in
      let _ = E.EventSet.iter
                (fun x -> debug_event chan x)
                e in
      print_string "]\n"

    let debug_cnstrnts chan e = fprintf chan "\n[ %s ]" (S.M.VC.pp_cnstrnts e)

    let debug_set chan r =
      E.EventRel.pp chan ","
        (fun chan (e1, e2) -> fprintf chan "%a -> %a"
                                debug_event e1 debug_event e2)
        r

    let debug_rel chan r =
      E.EventRel.pp chan ","
        (fun chan (e1, e2) -> fprintf chan "%a -> %a"
                                debug_event e1 debug_event e2)
        r

    let debug_procs chan procs =
      List.iter
        (fun (x, y) ->
          let _ = printf "proc %d \t:" x in
          debug_event_set stdout y) procs

(*    let debug_rf chan wt rf =
      let _ = match wt with
        | M.S.Final loc -> fprintf chan "Final %s ->" (A.pp_location loc)
        | M.S.Load ev -> debug_event chan ev in
      match rf with
      | M.S.Init -> fprintf chan "init\n"
      | M.S.Store ev ->let _ = debug_event chan ev in
                       print_string "\n"*)

    let debug_exec chan ex =
      let _ = fprintf chan "execution\n\npo : " in
      let _ = debug_rel chan (E.EventRel.remove_transitive_edges (E.EventRel.restrict_domains E.is_mem E.is_mem ex.po)) in
      let _ = fprintf chan "\n\nmo : " in
      let _ = debug_rel chan (E.EventRel.remove_transitive_edges ex.mo) in
      let _ = fprintf chan "\n\nrf : " in
      let _ = debug_rel chan ex.rf in
      let _ = fprintf chan "\n\nadded : " in
      let _ = debug_event_set chan ex.added in
      let _ = fprintf chan "\ntoadd : " in
      let _ = debug_procs chan ex.toadd in
      let _ = fprintf chan "\nrevisit : " in
      let _ = debug_event_set chan ex.revisit in
(*      let _ = fprintf chan "log : " in
      let _ = List.iter (fun (x, y) -> fprintf chan " %s -" x) ex.log in*)
      fprintf chan "\n--------------------\n\n"



      (* relations and events *)

    let aux0 f0 f1 a b =
      f1 a b (f0 a b)

    let events = ref E.EventSet.empty

    let all_locations () =
      E.EventSet.fold (fun e l ->
          match E.location_of e with
          | Some x -> M.S.A.LocSet.add x l
          | None -> l) !events M.S.A.LocSet.empty

    let location_is lo ev = match E.location_of ev with
      | Some x -> x = lo
      | _ -> false

    let aux = fun x ->
      try List.assoc x S.E.Act.arch_sets
      with Not_found -> fun x -> true

    let rlx = aux "RLX"
    let acq = aux "ACQ"
    let rel = aux "REL"
    let acq_rel = aux "AQU_REL"
    let sc = aux "SC"
    let na = aux "NA"
    let fence = E.is_barrier
    let a = aux "A"

    let seq_union a b =
      aux0 E.EventRel.sequence (fun x y z -> E.EventRel.union x z) a b

    let added a r = E.EventRel.restrict_domains
                      (fun x -> E.EventSet.mem x a)
                      (fun x -> E.EventSet.mem x a)
                      r

    let sbrf ex =
      added ex.added (E.EventRel.transitive_closure (E.EventRel.union (added ex.added ex.po) ex.rf))

    let hb rf po rmws =

      let mpo = E.EventRel.restrict_domains
                  E.is_mem
                  E.is_mem
                  po in
      let rseq = M.S.A.LocSet.fold
                (fun x rs ->
                  let rs0 = E.EventRel.sequence rf rmws in
                  let rs1 = E.EventRel.transitive_closure rs0 in
                  let rs2 = E.EventRel.restrict_domain
                              (fun y -> E.is_mem_store y
                                        && location_is x y
                                        && not (na y.E.action))
                              rs1 in
                  let rs3 = E.EventRel.restrict_domain
                              (fun y -> E.is_mem_store y
                                        && location_is x y)
                              mpo in
                  let rs4 = E.EventRel.sequence rs3 rs2 in
                  let rs5 = E.EventRel.restrict_rel
                              (fun y z -> location_is x y
                                          && location_is x z
                                          && E.is_mem_store y
                                          && E.is_mem_store z
                                          && not (na z.E.action))
                              mpo in
                  E.EventRel.union4 rs2 rs4 rs5 rs)
                (all_locations ())
                E.EventRel.empty in

      let sw0 = E.EventRel.sequence rseq rf in
      let sw1 = E.EventRel.restrict_codomain
                  (fun x ->
                    E.is_mem_load x
                    && (rlx x.E.action
                    || rel x.E.action
                    || acq x.E.action
                    || sc x.E.action))
                  sw0 in
      let sw2 = E.EventRel.restrict_domain (fun x -> fence x) mpo in
      let sw3 = E.EventRel.sequence sw2 sw1 in
      let sw4 = E.EventRel.union sw1 sw3 in
      let sw5 = E.EventRel.restrict_codomain (fun x -> fence x) mpo in
      let sw6 = E.EventRel.sequence sw4 sw5 in
      let sw7 = E.EventRel.union sw4 sw6 in
      let sw = E.EventRel.restrict_rel
                 (fun x y ->
                   (rel x.E.action
                    || sc x.E.action)
                   && (acq y.E.action
                       || sc y.E.action))
                 sw7 in

      let hb0 = E.EventRel.union mpo sw in
      E.EventRel.transitive_closure hb0

    let is_exval rmws e = E.EventRel.exists
                        (fun (x, _) -> E.same_location x e)
                        rmws

    let is_exclusive rmws e = E.EventRel.exists
                                (fun (x, y) -> x = e
                                               || y = e)
                                rmws



      (* preproc *)


    let solve test es cs =
      match M.solve_regs test es cs with
      | None -> (es, M.S.RFMap.empty, cs)
      | Some (es, rfm, cs) -> (es, rfm, cs)

(*    let is_annot = List.assoc "annot" E.Act.arch_sets*)

(*    let remove_events e =
      E.EventSet.filter
        (fun x ->
          match E.Act.value_of x.E.action with
          | Some E.Act.A.V.Val (Constant.Symbolic _) when is_annot x.E.action -> false
          | _ -> true)
        e*)

      (* postproc *)

    let clean_exec e =
      let nrf = E.EventRel.remove_transitive_edges e.rf in
      let nmo = E.EventRel.remove_transitive_edges e.mo in
      let npo = E.EventRel.remove_transitive_edges e.po in
      {e with rf = nrf; po = npo; mo = nmo}

    let check_exec ex =
      if E.EventRel.exists
           (fun (x, y) -> not (E.EventSet.mem x ex.added) || not (E.EventSet.mem y ex.added))
           (E.EventRel.union ex.rf ex.mo)
      then false
      else true



      (* assigning variables *)

    let is_final_write w ex =
      not (E.EventSet.exists
             (fun x -> E.same_location w x
                       && E.is_mem_store x)
             (E.EventSet.remove w
                (E.EventRel.succs (hb ex.rf ex.po ex.rmws) w)))
      && E.is_mem_store w

    let make_rfmap ex =
      let m = E.EventRel.fold (fun rel map ->
                  let key =
                    if is_final_write (fst rel) ex
                    then match (E.location_of (fst rel)) with
                         | Some x -> M.S.Final x
                         | None -> assert false
                    else M.S.Load (snd rel) in
                  M.S.RFMap.add key (M.S.Store (fst rel)) map) ex.rf ex.rfm in
      let m0 = M.S.A.LocSet.fold
                 (fun l map ->
                   try
                     let _ = M.S.RFMap.find (M.S.Final l) map in
                     map
                   with Not_found ->
                         try
                           let iswrite = fun x ->
                             E.is_mem_store x
                             && match E.location_of x with
                                | Some y when y = l -> true
                                | _ -> false in
                           let last0 = E.EventRel.restrict_domains
                                         iswrite
                                         iswrite
                                         (hb ex.rf ex.po ex.rmws) in
                           let last = E.EventSet.choose (E.EventRel.leaves last0) in
                           M.S.RFMap.add (M.S.Final l) (M.S.Store last) map
                 with Not_found -> map) (all_locations ()) m in
      m0

    let make_cnstrnts ex =
        E.EventRel.fold
          (fun rel cns ->
            match (E.written_of (fst rel), E.read_of (snd rel)) with
            | Some w, Some v ->
               M.S.M.VC.Assign (v, M.S.M.VC.Atom w) :: cns
            | _ -> cns) ex.rf []



      (* stateless algorithm aux functions *)


    let nextp exec po revisit pending =
      let rec aux e p = begin
          match e with
          | [] -> None
          | (_, e) :: tl ->
             try
               match E.EventRel.roots
                       (E.EventRel.restrict_rel
                          (fun x y -> E.EventSet.mem x e
                                      && E.EventSet.mem y e)
                          p) with
               | x when E.EventSet.is_empty x
                        && E.EventSet.is_empty e -> aux tl p
               | x when E.EventSet.is_empty x -> Some (E.EventSet.choose e)
               | x -> Some (E.EventSet.choose x)
             with Not_found -> None end in
      try match E.EventSet.cardinal pending with
          | 2 -> (Some (E.EventSet.find (fun x -> not (E.EventSet.mem x revisit)) pending))
          | 1 -> (Some (E.EventSet.choose pending))
          | 0 -> aux exec po
          | _ -> assert false
      with Not_found -> None

    let extract_event exec po revisit pending = match nextp exec po revisit pending with
      | None -> (None, exec)
      | Some e -> (Some e, List.map
                             (fun (x, y) -> (x, E.EventSet.remove e y))
                             exec)

    let pending ex =
      let cpo =
        E.EventRel.restrict_codomain
          (fun x -> E.EventSet.mem x ex.added)
          ex.po in
      let crmw = E.EventRel.restrict_domain
                   (fun x -> E.EventSet.mem x ex.added) ex.rmws in
      E.EventRel.codomain
        (E.EventRel.restrict_domains
           (fun x -> not (E.EventRel.exists
                            (fun (y, z) -> y = x)
                            cpo))
           (fun x -> not (E.EventSet.mem x ex.added))
        crmw)

    let return_events toadd g =
      let insert_event toadd e =
        List.map (fun (x, y) ->
            match E.proc_of e with
            | Some p when x = p -> (x, E.EventSet.add e y)
            | _ -> (x, y)) toadd in
      E.EventSet.fold (fun x y -> insert_event y x) g toadd

    let set_rf ex w r =
      let nrf0 = E.EventRel.restrict_codomain
                   (fun x -> not (E.EventSet.mem x r))
                   ex.rf in
      let nrf = E.EventRel.union
                  (E.EventRel.cartesian (E.EventSet.of_list [w]) r)
                  nrf0 in
      let out = {ex with rf = nrf} in
      out

    let insert_mo ex wp w =
      let m = E.EventRel.restrict_rel
                (fun x y -> x != w && y != w)
                ex.mo in

      let mo0 = E.EventRel.restrict_codomain
                  (fun x -> x = wp)
                  m in
      let mo1 = E.EventRel.domain mo0 in
      let mo2 = E.EventSet.add wp mo1 in
      let mo3 = E.EventRel.cartesian mo2 (E.EventSet.of_list [w]) in

      let mo4 = E.EventRel.restrict_domain
                  (fun x -> x = wp)
                  m in
      let mo5 = E.EventRel.codomain mo4 in
      let mo6 = E.EventRel.cartesian (E.EventSet.of_list [w]) mo5 in

      let mo7 = E.EventRel.union mo3 mo6 in

      let out = {ex with mo = E.EventRel.union ex.mo mo7} in
      out



      (* the algorithm itself *)


    let rec visit_write (ex : exec) w kont res =
      let _ =
        if debug
        then let _ = printf "\nvisiting write : " in
             let _ = debug_event stdout w in
             let _ = debug_exec stdout ex in
             printf "\nhb : %a\n" debug_rel (hb ex.rf ex.po ex.rmws)
        else () in
      (*      let _ = if check_exec ex then () else assert false in*)
      let r0 = E.EventRel.sequence ex.rf (added ex.added ex.rmws) in
      let r1 = E.EventRel.restrict_codomain
                 (fun x -> x = w)
                 r0 in

      if not (E.EventRel.is_empty r1) then
        let wp = E.EventSet.choose (E.EventRel.domain r1) in
        revisit_reads (insert_mo {ex with log = List.append ex.log ["rvr " ^ E.pp_action w ^ "," ^ E.EventSet.fold (fun x y -> E.pp_action x ^ " " ^ y) ex.revisit "", ex]} wp w) w kont res

      else
        let m1 = E.EventRel.restrict_rel
                   (fun x y -> E.same_location w x)
                   ex.mo in
        let w0 = try
            E.EventSet.choose (E.EventRel.leaves m1)
          with Not_found -> try E.EventSet.choose
                                  (E.EventSet.filter
                                     (fun x -> E.is_mem_store x
                                               && E.same_location x w
                                               && x != w)
                                     ex.added)
                            with Not_found -> assert false in
        let rvr = revisit_reads
                    (insert_mo
                       {ex with log = List.append ex.log ["rvr " ^ E.pp_action w ^ "," ^ E.EventSet.fold (fun x y -> E.pp_action x ^ " " ^ y) ex.revisit "", ex]} w0 w)
                    w kont res in

        let hb0 = hb ex.rf ex.po ex.rmws in
        let s0 = E.EventRel.restrict_codomain (fun x -> x = w) hb0 in
        let s1 = E.EventRel.sequence ex.rf s0 in
        let s2 = E.EventRel.union s0 s1 in
        let s3 = E.EventRel.sequence ex.mo s2 in

        let s4 = E.EventRel.restrict_codomain
                   (fun x -> E.is_mem_load x
                             && is_exclusive ex.rmws x)
                   ex.rf in
        let s5 = E.EventRel.union s3 s4 in
        let s6 = E.EventRel.domain s5 in
        let s7 = E.EventSet.filter
                   (fun x -> E.is_mem_store x
                             && E.same_location w x)
                   ex.added in
        let s = E.EventSet.filter
                  (fun x -> x != w0
                            && not (E.EventSet.mem x s6)
                            && w != x)
                  s7 in

        let sbr = sbrf ex in

        E.EventSet.fold
          (fun x res1 ->

            let sb0 = E.EventRel.reachable x ex.mo in
            let sb1 = E.EventRel.restrict_codomain (fun y -> E.EventSet.mem y sb0 || y = w) sbr in
            let sb2 = E.EventRel.domain sb1 in
            let sb3 = E.EventSet.add w sb2 in
            let nrevisit = E.EventSet.filter
                             (fun x -> not (E.EventSet.mem x sb3))
                             ex.revisit in
            (revisit_reads
               (insert_mo
                  {ex with revisit = nrevisit;
                           log = List.append ex.log ["rvr " ^ E.pp_action w ^ "," ^ E.EventSet.fold (fun x y -> E.pp_action x ^ " " ^ y) ex.revisit "", ex]}
                  x
                  w)
               w kont res1)) (E.EventSet.remove w0 s) rvr

    and revisit_reads ex w kont res =
      let _ =
        if debug
        then let _ = printf "\nrevisiting reads for write : " in
             let _ = debug_event stdout w in
             let _ = debug_exec stdout ex in
             printf "\nhb : %a\n" debug_rel (hb ex.rf ex.po ex.rmws)
        else () in

      (*      let _ = if check_exec ex then () else assert false in*)

      let mpo = added ex.added ex.po in

      let r0 = E.EventSet.filter
                 (E.same_location w)
                 ex.revisit in

      let sbr = sbrf ex in
      let hbf = hb ex.rf mpo ex.rmws in

      let r1 = E.EventRel.restrict_codomain
                 (fun x -> x = w)
                 sbr in
      let r2 = E.EventSet.diff r0 (E.EventRel.domain r1) in

      let r3 = seq_union ex.mo ex.rf in
      let r4 = seq_union r3 hbf in
      let r5 = E.EventRel.sequence r4 mpo in
      let r5b = E.EventRel.restrict_domain (fun x -> x = w) r5 in
      let r6 = E.EventSet.diff r2 (E.EventRel.codomain r5b) in

      let km0 = E.EventRel.sequences [E.EventRel.inverse ex.rf; ex.rf; added ex.added ex.rmws] in
      let km1 = E.EventRel.restrict_domains
                  (fun x -> E.is_mem_store x
                            && is_exclusive ex.rmws x)
                  (fun x -> x = w)
                  km0 in
      let km2 = E.EventRel.diff km1 ex.rmws in
      let kmust = E.EventRel.domain km2 in

      let r7 = E.EventRel.restrict_domain
                 (fun x -> E.EventSet.mem x kmust)
                 sbr in
      let r8 = E.EventSet.union kmust (E.EventRel.codomain r7) in
      let r = E.EventSet.diff r6 r8 in

      let sbr2 = E.EventRel.union sbr (E.EventRel.inverse sbr) in
      let kl0 = E.EventSet.fold
                  (fun e l ->
                    List.append
                      l
                      (List.map
                         (fun x -> E.EventSet.add e x)
                         (List.filter
                            (fun x -> not (E.EventRel.exists
                                             (fun (y, z) -> E.EventSet.mem y x
                                                            && z = e)
                                             sbr2 || E.is_mem_store_init e))
                            l)))
                  r [E.EventSet.empty] in
      let kl = List.filter
                 (fun x -> E.EventSet.cardinal
                             (E.EventSet.filter
                                (fun y -> is_exval ex.rmws y)
                                x) <= 1)
                 kl0 in
      let _  = if E.EventSet.is_empty (E.EventSet.filter E.is_mem_store ex.revisit)
               then ()
               else printf "write in revisit" in

      (*      let _ = List.iter (fun x -> printf "subrevisits : %a\n" debug_event_set x) kl in*)

      List.fold_left
        (fun res1 k ->
          let k0 = E.EventRel.restrict_domain
                     (fun x -> E.EventSet.mem x k)
                     sbr in
          let k1 = E.EventRel.codomain k0 in
          let k2 = E.EventSet.filter
                     (fun x -> not (E.EventSet.mem x k1))
                     kmust in
          let k3 = E.EventSet.union k k2 in

          let g = E.EventRel.codomain (E.EventRel.restrict_domain
                                         (fun x -> E.EventSet.mem x k3)
                                         sbr) in
          let ntoadd = return_events ex.toadd g in
          let nadded = E.EventSet.filter
                         (fun x -> not (E.EventSet.mem x g))
                         ex.added in
          let nmo = added nadded ex.mo in
          let nrf = added nadded ex.rf in
          let nex = set_rf {ex with added = nadded; toadd = ntoadd; mo = nmo; rf = nrf} w k3 in

          let nrevisit0 = E.EventRel.restrict_codomain
                            (fun x -> E.EventSet.mem x k)
                            sbr in
          let nrevisit1 = E.EventSet.union (E.EventRel.domain nrevisit0) k in
          let nrevisit2 = E.EventSet.inter ex.revisit nex.added in
          let nrevisit = E.EventSet.filter
                           (fun x -> not (E.EventSet.mem x nrevisit1))
                           nrevisit2 in
          visit {nex with revisit = nrevisit;} kont res1)
        res kl

    and visit_read (ex : exec) r kont res =
      let _ =
        if debug
        then
          let _ = printf "\nvisiting read : " in
          let _ = debug_event stdout r in
          let _ = debug_exec stdout ex in
          printf "\nhb : %a\n" debug_rel (hb ex.rf ex.po ex.rmws)
        else
          () in

      (*      let _ = if check_exec ex then () else assert false in*)

      let w0 = E.EventSet.filter (fun x -> E.is_mem_store x && E.same_location r x) ex.added in
      let h = hb ex.rf ex.po ex.rmws in

      let c0 = E.EventRel.sequences [ex.mo; ex.rf; h] in
      let c1 = E.EventRel.sequence ex.mo h in
      let c2 = E.EventRel.union c0 c1 in
      let c3 = E.EventRel.restrict_codomain (fun x -> x = r) c2 in

      let w1 = E.EventSet.filter (fun x -> not (E.EventSet.mem x (E.EventRel.domain c3))) w0 in

      let a1 = E.EventSet.filter (fun x -> E.is_mem_store x && is_exval ex.rmws x) ex.added (*!events*) in

      (*      let a20 = E.EventRel.union ex.po ex.rf in
      let a21 = E.EventRel.transitive_closure a20 in (* sbrf *)*)
      let sbr = sbrf ex in
      let a22 = E.EventRel.restrict_rel
                  (fun x y -> E.is_mem_store x
                              && is_exclusive ex.rmws x
                              && E.EventSet.mem x ex.revisit
                              && y = r)
                  sbr in
      let a23 = E.EventRel.restrict_codomain
                  (fun x -> is_exclusive ex.rmws x
                            && E.is_mem_store x
                            && not (E.EventSet.mem x ex.revisit))
                  ex.rf in
      let a2 = E.EventRel.domain (E.EventRel.union a22 a23) in
      let w = E.EventSet.inter ex.added (E.EventSet.diff w1 (E.EventSet.inter a1 a2)) in

      let dsbr = E.EventRel.domain
                   (E.EventRel.restrict_codomain
                      (fun x -> x = r)
                      sbr) in

      let wx = try
          let wp = E.EventSet.choose (E.EventSet.inter w dsbr) in

          let rec aux wx =
            if is_exval ex.rmws wx then
              let t0 = E.EventRel.restrict_domain
                         (fun x -> x = wx)
                         ex.rf in
              let t1 = E.EventRel.sequence t0 (added ex.added ex.rmws) in
              let t2 = E.EventRel.restrict_codomain
                         (fun x -> E.EventSet.mem x ex.added)
                         t1 in
              if not (E.EventRel.is_empty t2)
              then aux (E.EventSet.choose (E.EventRel.codomain t2))
              else wx
            else wx in

          aux wp with Not_found -> E.EventSet.choose w in
      if not (E.EventSet.mem wx ex.added) then assert false else
        let res0 = visit (set_rf {ex with revisit = E.EventSet.add r ex.revisit}
                            wx
                            (E.EventSet.of_list [r]))
                     kont
                     res in

        E.EventSet.fold
          (fun x res1 ->
            let nrevisit =
              E.EventSet.diff ex.revisit
                (E.EventRel.domain
                   (E.EventRel.restrict_codomain
                      (fun y -> y = r || y = x) sbr)) in
            visit (set_rf {ex with revisit = nrevisit} x (E.EventSet.of_list [r])) kont res1)
          (E.EventSet.remove wx w) res0

    and visit (ex : exec) kont res =
      (*      let _ =
        if debug then debug_exec stdout ex else () in*)
      let pending = pending ex in
      let a0 = extract_event ex.toadd ex.po ex.revisit pending in
      match a0 with
      | (Some e, ntoadd) -> begin
          let nadded = E.EventSet.add e ex.added in
          let newex = {ex with toadd = ntoadd; added = nadded;} in
          try match e with
              | x when E.is_mem_store x -> visit_write {newex with log = List.append newex.log ["vw " ^ E.pp_action x, ex]} e kont res
              | x when E.is_mem_load x -> visit_read {newex with log = List.append newex.log ["vl " ^E.pp_action x, ex]} e kont res
              | _ -> visit newex kont res
          with Not_found -> visit newex kont res
        end
      | None, _ ->
         let h = hb ex.rf ex.po ex.rmws in
         let r0 = E.EventRel.cartesian ex.added ex.added in
         let r1 = E.EventRel.restrict_rel
                    (fun x y -> E.same_location x y
                                && (E.is_mem_store x
                                    || E.is_mem_store y)
                                && not (E.is_mem_store_init x)
                                && not (E.is_mem_store_init y))
                    r0 in
         let r2 = E.EventRel.restrict_rel
                    (fun x y -> not (E.same_proc x y))
                    r1 in
         let r3 = E.EventRel.diff r2 (E.EventRel.union h (E.EventRel.inverse h)) in
         let dr = E.EventRel.restrict_rel
                    (fun x y -> not (a x.E.action
                                     && a y.E.action))
                    r3 in
         let sbl = E.EventRel.restrict_rel
                     (fun x y -> not (E.same_location x y))
                     ex.po in
         let hbl = E.EventRel.restrict_rel
                     E.same_location
                     h in

         let scb0 = E.EventRel.sequences [sbl; h; sbl] in
         let scb1 = E.EventRel.sequence (E.EventRel.inverse ex.rf) ex.mo in
         let scb = E.EventRel.union5 ex.po scb0 hbl ex.mo scb1 in

         let psc0 = E.EventRel.restrict_domain
                      (fun x -> fence x
                                && sc x.E.action)
                      h in
         let psc1 = E.EventRel.sequence psc0 scb in
         let psc2 = E.EventRel.restrict_domain (fun x -> sc x.E.action) scb in
         let psc3 = E.EventRel.union psc1 psc2 in
         let psc4 = E.EventRel.restrict_codomain (fun x -> sc x.E.action) psc3 in
         let psc5 = E.EventRel.restrict_codomain
                      (fun x -> fence x
                                && sc x.E.action)
                      h in
         let psc6 = E.EventRel.sequence psc3 psc5 in
         let psc7 = E.EventRel.union psc4 psc6 in

         let eco0 = E.EventRel.union3 ex.mo
                      ex.rf
                      (E.EventRel.sequence (E.EventRel.inverse ex.rf) ex.mo) in
         let eco = E.EventRel.transitive_closure eco0 in

         let psc10 = E.EventRel.union (E.EventRel.sequences [h; eco; h]) h in
         let psc11 = E.EventRel.restrict_rel
                       (fun x y -> fence x
                                   && fence y
                                   && sc x.E.action
                                   && sc y.E.action)
                       psc10 in
         let psc = E.EventRel.union psc7 psc11 in

         if
           not (E.EventRel.is_acyclic psc)(* && false*)
         then
           res
         else
           (*           let _ = debug_exec stdout ex in*)
           if E.EventRel.is_empty dr
           then kont (clean_exec {ex with psc = psc}) res
           else  kont (clean_exec {ex with flags = Flag.Set.add Flag.Undef ex.flags}) res

    let finals ex =
      E.EventSet.elements
        (E.EventSet.filter
           (fun x -> E.is_mem_store x
                     && E.EventSet.is_empty
                          (E.EventRel.succs
                             (E.EventRel.restrict_domains
                                (E.same_location x)
                                (E.same_location x)
                                ex.mo)
                             x))
           ex.added)

    let mykont test model_kont es cs = (fun e res ->
        M.solve_mem test es e.rfm (List.append cs (make_cnstrnts e))
          (fun es0 rfm0 cs0 res0 ->
            match cs0 with
            | [] ->
               if S.A.reject_mixed then M.check_sizes es0;
               if not (S.O.optace) || M.check_rfmap es0 rfm0
               then
                 let pp_relns =
                   lazy begin
                       ("mo", e.mo)::
                       ("hb", E.EventRel.remove_transitive_edges (hb e.rf e.po e.rmws))::
                       ("rf", e.rf)::
                       ("po", e.po)::
                       (*"revisit", E.EventRel.cartesian e.revisit e.revisit)::*)
                       ("rmw", e.rmws)::e.debug_rels
                     end in
                 let rfm = List.fold_left
                             (fun k w ->
                               M.S.RFMap.add (M.S.Final (M.get_loc w)) (M.S.Store w) k) rfm0 (finals e) in
                 let fsc = M.compute_final_state test rfm in
                 let conc =
                   {
                     S.str = es0;
                     rfmap = rfm;
                     fs = fsc;

                     po = E.EventRel.empty;
                     pos = E.EventRel.empty;
                     pco = E.EventRel.empty;

                     store_load_vbf = E.EventRel.empty;
                     init_load_vbf = E.EventRel.empty;
                     last_store_vbf = E.EventRel.empty;
                     atomic_load_store = E.EventRel.empty
                   } in
                 model_kont conc conc.S.fs pp_relns e.flags res0
               else begin
                   res0
                 end
            | _ -> M.when_unsolved test es0 rfm0 cs0 (fun c -> c) res0) res)

    let check_rfms test rfms kfail kont model_kont res =
      let (_, cs0, es0) = rfms in
      let (es, rfm, cs) = solve test es0 cs0 in
      let rmws = M.make_atomic_load_store es in
      let evts = es.E.events in
(*      let clean = E.EventSet.filter
                    (*fun x -> is_annot x.E.action*) (fun x -> not (E.is_mem x))
                    evts in
      let _ = printf "evts = %a\nclean = %a\n" debug_event_set evts debug_event_set clean in*)
      let inits = E.EventSet.filter E.is_mem_store_init evts in
(*      let notinits = E.EventSet.filter (fun x -> not (E.is_mem_store_init x)) evts in*)
      let po = (U.po_strict es) in
      let procs = List.map
                    (fun x ->
                      let e = E.EventSet.filter
                                (fun y -> match E.proc_of y with
                                          | Some p when p = x -> true
                                          | _ -> false)
                                evts in
                      x, e, E.EventRel.restrict_rel (fun x y -> E.EventSet.mem x e && E.EventSet.mem y e) po)
                    es.E.procs in
      let toadd = List.map (fun (x, y, z) -> x, y) procs in
      events := (E.EventSet.union evts inits);
      let ex_init = {
          toadd = toadd;
          added = inits;
          po = (E.EventRel.union rmws po);
          mo = E.EventRel.empty;
          rf = E.EventRel.empty;
          revisit = E.EventSet.empty;
          exvals = (fun x -> false);
          rmws = rmws;
          rfm = rfm;
          flags = Flag.Set.empty;
          log = [];
          psc = E.EventRel.empty;
          debug_rels = []
        } in
      (visit ex_init (mykont test model_kont es cs) res)

    let check_event_structure test (rfms : (_ * S.M.VC.cnstrnts * S.event_structure) list) kfail kont model_kont  (res : 'a)  =
      List.fold_left (fun re rf -> check_rfms test rf kfail kont model_kont re) res rfms

  end
