open Printf

module type Cfg = sig
  val skipchecks : StringSet.t
  include Mem.S
end

module Make (M:Cfg)
  =
  struct
    module S = M.S
    module E = S.E
    module A = S.A
    module U = MemUtils.Make(S)
    module Sol = E.Act.A.V.Solution

    type exec = {
        po : E.EventRel.t;
        iico : E.EventRel.t;
        mo : E.EventRel.t;
        rf : E.EventRel.t;
        toadd : (int * E.EventSet.t) list;
        added : E.EventSet.t;
        revisit : E.EventSet.t;
        safe : E.EventSet.t;
        rmws : E.EventRel.t;
        exvals : E.event -> bool;
        rfm : M.S.rfmap;
        flags : Flag.Set.t;
        psc : E.EventRel.t;
        debug_rels : (string * E.EventRel.t) list;
      }

              (* debug *)

    let debug = false

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

    let debug_rf chan wt rf =
      let _ = match wt with
        | M.S.Final loc -> fprintf chan "Final %s ->" (A.pp_location loc)
        | M.S.Load ev -> debug_event chan ev in
      match rf with
      | M.S.Init -> fprintf chan "init\n"
      | M.S.Store ev ->let _ = debug_event chan ev in
                       print_string "\n"

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
      let _ = printf "rmws = %a\n" debug_rel ex.rmws in
      fprintf chan "\n--------------------\n\n"



      (* relations and events *)

    let aux0 f0 f1 a b =
      f1 a b (f0 a b)

    let aux = fun x ->
      try List.assoc x S.E.Act.arch_sets
      with Not_found ->
        let _ = fprintf stderr "not found %s\n" x in fun x -> true

    let rmw = aux "RMW"
    let rlx = aux "RLX"
    let acq = aux "ACQ"
    let rel = aux "REL"
    let acq_rel = aux "ACQ_REL"
    let sc = aux "SC"
    let na = aux "NA"
    let fence = E.is_barrier
    let atomic = aux "A"


    (* a; b? *)
    let seq_union a b =
      aux0 E.EventRel.sequence (fun x y z -> E.EventRel.union x z) a b


    let added a r = E.EventRel.restrict_domains
                      (fun x -> E.EventSet.mem x a)
                      (fun x -> E.EventSet.mem x a)
                      r

                      (* sbr = (sb | rf)+ *)
    let sbrf ex =
      added ex.added (E.EventRel.transitive_closure (E.EventRel.union (added ex.added ex.po) ex.rf))

            (* rseq = [W]; (sb & loc)?; [W & (RLX | REL | ACQ_REL | ACQ | SC)]; (rf; rmw)* *)
    let rseq ex =
      let rs0 = E.EventRel.restrict_rel
                  E.same_location
                  ex.po in
      let rs1 = E.EventRel.set_to_rln
                  (E.EventSet.filter E.is_mem_store ex.added) in
      let rs2 = E.EventRel.sequence rs1 rs0 in
      let rs3 = E.EventRel.set_to_rln
                  (E.EventSet.filter (fun x -> E.is_mem_store x
                                               && (rlx x.E.action
                                                   || rel x.E.action
                                                   || acq x.E.action
                                                   || acq_rel x.E.action
                                                   || sc x.E.action))
                     ex.added) in
      let rs4 = E.EventRel.sequence rs2 rs3 in
      let rs5 = E.EventRel.inter rs1 rs3 in
      let rs6 = E.EventRel.union rs4 rs5 in
      let rs7 = E.EventRel.transitive_closure (E.EventRel.sequence ex.rf (added ex.added ex.rmws)) in
      E.EventRel.union rs6 (E.EventRel.sequence rs6 rs7)

                       (* sw = [(REL | ACQ_REL | SC)]; ([F]; sb)?; rs; rf; [R & (RLX | REL | ACQ | ACQ_REL | SC)]; (sb; [F])?; [(ACQ | ACQ_REL | SC)] *)
      let sw ex =
      let mpo = ex.po in
      let rseq = rseq ex in
      let fences = E.EventSet.filter
                     fence
                     ex.added in

      let sw0 = E.EventRel.sequence rseq ex.rf in
      let sw1 = E.EventRel.set_to_rln (E.EventSet.filter
                                         (fun x -> rel x.E.action
                                                   || acq_rel x.E.action
                                                   || sc x.E.action)
                                         ex.added) in
      let sw2 = E.EventRel.sequence (E.EventRel.set_to_rln fences) mpo in
      let sw3 = E.EventRel.union sw1 (E.EventRel.sequence sw1 sw2) in
      let sw4 = E.EventRel.sequence sw3 sw0 in
      let sw5 = E.EventRel.set_to_rln (E.EventSet.filter
                                         (fun x -> (rlx x.E.action
                                                    || rel x.E.action
                                                    || acq x.E.action
                                                    || acq_rel x.E.action
                                                    || sc x.E.action)
                                                   && E.is_mem_load x)
                                         ex.added) in
      let sw6 = E.EventRel.sequence sw4 sw5 in
      let sw7 = E.EventRel.sequence mpo (E.EventRel.set_to_rln fences) in
      let sw8 = E.EventRel.set_to_rln (E.EventSet.filter
                                     (fun x -> acq x.E.action
                                               || acq_rel x.E.action
                                               || sc x.E.action)
                                     ex.added) in
      let sw9 = E.EventRel.union sw8
              (E.EventRel.sequence sw7 sw8) in
      let sw = E.EventRel.sequence sw6 sw9 in
      sw

      (* hb = (sb | sw)+ *)
    let hb ex =

      let sw0 = sw ex in
      let hb0 = E.EventRel.union ex.po sw0 in
      E.EventRel.transitive_closure hb0

    (* is part of a rmw operation *)
    let is_exclusive rmws e = E.EventRel.exists
                                (fun (x, y) -> x = e
                                               || y = e)
                                rmws



      (* preproc *)


    let solve test es cs =
      match M.solve_regs test es cs with
      | None -> (es, M.S.RFMap.empty, cs)
      | Some (es, rfm, cs) -> (es, rfm, cs)



      (* postproc *)

    let clean_exec e =
      let nrf = E.EventRel.remove_transitive_edges (E.EventRel.restrict_domains E.is_mem E.is_mem e.rf) in
      let nmo = E.EventRel.remove_transitive_edges (E.EventRel.restrict_domains E.is_mem E.is_mem e.mo) in
      let npo = E.EventRel.remove_transitive_edges (E.EventRel.restrict_domains E.is_mem E.is_mem e.po) in
      {e with rf = nrf; po = npo; mo = nmo}



      (* assigning variables *)

    let is_final_write w ex =
      E.is_mem_store w
      && not (E.EventRel.exists
                (fun (x, _) -> x = w)
                ex.mo)


    let make_cnstrnts ex =
        E.EventRel.fold
          (fun rel cns ->
            match (E.written_of (fst rel), E.read_of (snd rel)) with
            | Some w, Some v ->
               M.S.M.VC.Assign (v, M.S.M.VC.Atom w) :: cns
            | _ -> cns) ex.rf []



      (* stateless algorithm aux functions *)

      (* next event : pending write if there is one or next event according to thread number ascending order and po *)
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
                    (* pending write : not yet added write of a rmw whose read has been added *)
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

    let check_revisit ex =
      let t0 = (E.EventRel.codomain (added ex.added (E.EventRel.sequences [E.EventRel.set_to_rln ex.revisit; sbrf ex; E.EventRel.set_to_rln (E.EventSet.filter (fun x -> E.is_mem_load x && not (E.is_mem_store x)) ex.added)]))) in
      if
        not (E.EventSet.subset t0 ex.revisit)
      then
        let _ = if debug then printf "4.1.1\n" else () in
        false
      else
        true

    let check_exec ex =
      let c1 = E.EventRel.filter
                 (fun (x, y) -> not (E.EventSet.mem x ex.added) || not (E.EventSet.mem y ex.added))
                 (E.EventRel.union ex.rf ex.mo) in
      if not (E.EventRel.is_empty c1)
      then
        let _ = if debug then printf "%a\n%a\n" debug_exec ex debug_rel c1 else () in
        false
      else if E.EventSet.exists
                   (fun x -> E.EventRel.cardinal
                           (E.EventRel.restrict_codomain (fun y -> y = x) ex.rf)
                           != 1)
                   (E.EventSet.filter E.is_mem_load ex.added)
      then
        let _ = if debug then printf "2 : %a\n%a\n" debug_rel ex.rf debug_event_set (E.EventSet.filter (fun x -> E.is_mem_load x && not (E.is_mem_store x)) ex.added) else () in
        false
      else
        let grp = E.EventSet.filter
                    (is_exclusive ex.rmws)
                    (pending ex) in
        let t1 = E.EventRel.sequences [E.EventRel.set_to_rln grp;
                                       E.EventRel.inverse ex.rf;
                                       ex.rf;
                                       E.EventRel.set_to_rln (E.EventSet.diff
                                                                (E.EventSet.filter
                                                                   (is_exclusive ex.rmws)
                                                                   ex.added)
                                                                grp)] in
        if not (E.EventRel.is_empty
                  (E.EventRel.restrict_rel
                     (fun x y -> not (E.EventSet.mem y ex.revisit)
                                 || E.EventSet.mem x ex.revisit)
                     t1))
        then
          false
        else
          true

      let check_cns ex cs =
        let ncs = (List.append cs (make_cnstrnts
                                     {ex with rf = added ex.safe ex.rf})) in
        match M.S.M.VC.solve ncs with
        | M.S.M.VC.NoSolns -> false
        | _ -> true



    (* return events in g to their respective threads in toadd *)
    let return_events toadd g =
      let insert_event toadd e =
        List.map (fun (x, y) ->
            match E.proc_of e with
            | Some p when x = p -> (x, E.EventSet.add e y)
            | _ -> (x, y)) toadd in
      E.EventSet.fold (fun x y -> insert_event y x) g toadd

    (* modify ex.rf such that all the reads in r read from w *)
    let set_rf ex w r =
      let nr = E.EventSet.inter ex.added r in
      let nrf0 = E.EventRel.restrict_codomain
                   (fun x -> not (E.EventSet.mem x nr))
                   ex.rf in
      let nrf = E.EventRel.union
                  (E.EventRel.cartesian (E.EventSet.of_list [w]) nr)
                  nrf0 in
      let out = {ex with rf = nrf} in
      out

    (* returns the event a such that (e,a) in mo but there exists no b such that (e,b) and (e,a) in mo *)
    let succ mo e =
      let s0 = E.EventRel.restrict_domain
                 (fun x -> x = e)
                 mo in
      let s1 = E.EventRel.restrict_domains
                 (fun x -> E.EventSet.mem x (E.EventRel.codomain s0))
                 (fun x -> E.EventSet.mem x (E.EventRel.codomain s0))
                 mo in
      let out = E.EventRel.roots s1 in
      match E.EventSet.cardinal out with
      | 0 | 1 -> out
      | _ -> assert false


    let check_reads ex =
      not (E.EventSet.exists
        (fun x -> E.EventRel.cardinal (E.EventRel.restrict_codomain (fun y -> y = x) ex.rf) != 1)
        (E.EventSet.filter E.is_mem_load ex.added))


    (* put wp after w in mo *)
    let insert_mo ex wp w =
      let _ = assert (check_reads ex) in
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

      let extend_safe ex w =
        let sbr = sbrf ex in
        let r0 = E.EventRel.restrict_domains
               (fun x -> E.EventSet.mem x ex.revisit)
               (fun x -> x = w)
               sbr in
        if E.EventRel.is_empty r0
        then (true, {ex with safe = E.EventSet.add w ex.safe})
        else (false, ex)


      let hbeco ex =
(*        let h0 = hb ex in
        let rf0 = E.EventRel.inverse ex.rf in
        let r0 = E.EventRel.union ex.mo (E.EventRel.sequence rf0 ex.mo) in
        let r1 = E.EventRel.union r0 (E.EventRel.sequence r0 ex.rf) in
        E.EventRel.sequence r1 h0*)

        let h0 = hb ex in
        let h = E.EventRel.union ex.rmws h0 in
        let rb0 = E.EventRel.sequence (E.EventRel.inverse ex.rf) ex.mo in
        let rb = E.EventRel.restrict_rel (fun x y -> x != y) rb0 in
        let eco = E.EventRel.transitive_closure (E.EventRel.union3 ex.rf ex.mo rb) in
(*        let r0 = E.EventRel.sequence eco h in
        let r1 = E.EventRel.sequence r0 eco in
        let r2 = E.EventRel.union r0 r1 in
        let r3 = E.EventRel.sequence h eco in
        E.EventRel.union3 h r2 r3*)
        E.EventRel.union h (E.EventRel.sequence h eco)



      (* the algorithm itself *)


      let rec visit_write ex cs w kont res =
        (*        if E.EventRel.is_irreflexive (hbeco ex) then*)
        (*          let _ = printf "write\n" in*)
        let s0 = E.EventSet.filter (fun x -> E.is_mem_store x && E.same_location x w) ex.added in

        let h = hb ex in
        let s1 = E.EventRel.sequences [ex.mo; ex.rf; h; E.EventRel.singleton (w, w)] in
        let s2 = E.EventRel.sequences [ex.mo; h; E.EventRel.singleton (w, w)] in
        let s3 = E.EventRel.union s1 s2 in
        let s4 = E.EventSet.diff s0 (E.EventRel.domain s3) in
        let s5 = E.EventSet.remove w s4 in
        (*          let s5 = E.EventSet.remove w s0 in*)
        let w0 = try
            E.EventSet.choose (E.EventRel.leaves (E.EventRel.restrict_domain (E.same_location w ) ex.mo))
          with Not_found -> E.EventSet.choose (E.EventSet.filter (fun x -> E.is_mem_store_init x && E.same_location x w) ex.added) in
        let nex = insert_mo ex w0 w in
        let res0 = revisit_reads nex cs w kont res in
        let s = E.EventSet.remove w0 s5 in
        (*        let s = s0 in*)
        E.EventSet.fold
          (fun wp res1 ->
            let nex = insert_mo ex wp w in
            revisit_reads nex cs w kont res1
          ) s res0
      (*       else
          res*)

      and revisit_reads ex cs w kont res =
        (*        if E.EventRel.is_irreflexive (hbeco ex) then*)
        (*          let _ = printf "revisit\n" in*)
        let r0 = E.EventSet.filter (fun x -> E.is_mem_load x && E.same_location x w) ex.revisit in
        let r1 = E.EventRel.sequence (E.EventRel.singleton (w, w)) ex.mo in
        let r2 = E.EventRel.sequence r1 ex.rf in
        let r3 = E.EventRel.union r1 r2 in
        let h = hb ex in
        let r4 = E.EventRel.sequence r3 h in
        let r5 = E.EventRel.union r3 r4 in
        let r6 = E.EventRel.sequence r5 (added ex.added ex.po) in
        let r7 = E.EventSet.inter (E.EventRel.codomain r6) r0 in
        let r = E.EventSet.diff r0 (E.EventRel.codomain r6) in

        (*        let r8 = E.EventRel.sequence sbr (E.EventRel.singleton (w, w)) in
        let r = E.EventSet.diff r7 (E.EventRel.domain r8) in*)
        (*        let r = r0 in*)
        (*        let rb0 = E.EventRel.sequence (E.EventRel.inverse ex.rf) ex.mo in
        let rb = E.EventRel.restrict_rel (fun x y -> x != y) rb0 in*)
        (*        let eco = E.EventRel.transitive_closure (E.EventRel.union3 ex.rf ex.mo rb) in*)
        (*        let r6 = E.EventRel.sequence (hbeco ex) (E.EventRel.singleton (w, w)) in
        let r = E.EventSet.diff r0 (E.EventRel.domain r6) in*)
        let kl0 = E.EventSet.fold
                   (fun e l ->
                     List.append
                       l
                       (List.map
                          (fun x -> E.EventSet.add e x)
                          l))
                   r [E.EventSet.empty] in
        let sbr = added ex.added ex.po in
        let kl = List.filter
                   (fun x -> not (E.EventRel.exists
                                    (fun (y, z) -> E.EventSet.mem y x
                                                   && E.EventSet.mem z x)
                                    sbr))
                   kl0 in
        List.fold_left
          (fun res1 k1 ->
            let nex = set_rf ex w k1 in
            let g0 = E.EventRel.restrict_domain (fun x -> E.EventSet.mem x k1) sbr in
            let g1 = E.EventRel.codomain g0 in
            let g = E.EventSet.filter (fun x -> E.is_mem_load x && E.same_location x w) g1 in
            let ntoadd = return_events nex.toadd g in
            let nadded = E.EventSet.diff nex.added g in
            let nrf = added nadded nex.rf in
            let nmo = added nadded nex.mo in
            let nex0 = {nex with toadd = ntoadd;
                            added = nadded;
                            mo = nmo;
                            rf = nrf} in
            let nr0 = added nex0.added nex0.po in
            let nr1 = E.EventRel.restrict_domains (fun x -> E.same_location w x) (fun x -> E.EventSet.mem x k1) nr0 in
            let nr2 = E.EventSet.union k1 (E.EventRel.domain nr1) in

            let _ = if (check_reads nex0) then () else let _ = printf "old : %a\nnew : %a\nk1 = %a\nw = %a\n" debug_exec ex debug_exec nex debug_event_set k1 debug_event w in assert false in
            if E.EventRel.is_irreflexive (hbeco nex0) then
              visit {nex0 with revisit = E.EventSet.diff nex.revisit nr2(*E.EventSet.union nr2 r7*)} cs kont res1
            else res1
          )
          res kl
      (*        else res*)

      and visit_read (ex : exec) cs r kont res =
        (*        if E.EventRel.is_irreflexive (hbeco ex) then*)
        (*          let _ = printf "read\n" in*)
        let w0 = E.EventSet.filter (fun x -> E.is_mem_store x && E.same_location r x) ex.added in

        let h = hb ex in
        let w1 = E.EventRel.sequences [ex.mo; ex.rf; h; E.EventRel.singleton (r, r)] in
        let w2 = E.EventRel.sequences [ex.mo; h; E.EventRel.singleton (r, r)] in
        let w3 = E.EventRel.union w1 w2 in
        let w4 = E.EventSet.diff w0 (E.EventRel.domain w3) in
        let w = w4 in
        (*          let w = w0 in*)

        let wx = try E.EventSet.choose w with Not_found -> E.EventSet.choose (E.EventSet.filter (fun x -> E.is_mem_store_init x && E.same_location x r) ex.added) in
        let ex0 = set_rf {ex with revisit = E.EventSet.add r ex.revisit} wx (E.EventSet.singleton r) in
        let _ = if (check_reads ex0) then () else let _ = printf "%a\n" debug_exec ex0 in assert false in
        let res0 = visit ex0 cs kont res in
        E.EventSet.fold
          (fun x res1 ->
            let nex = set_rf ex x (E.EventSet.singleton r) in
            let _ = assert (check_reads ex0) in
            visit {nex with revisit = E.EventSet.add r ex.revisit} cs kont res1
          )
          (E.EventSet.remove wx w) res0
      (*        else res*)

      and visit (ex : exec) cs kont res =
        if (*E.EventRel.is_irreflexive (hbeco ex)*) true then
          (*          let _ = printf "visit\n" in*)
          let _ = assert (E.EventSet.is_empty (E.EventSet.diff ex.safe ex.added)) in
          let pending = E.EventSet.empty in
          let a0 = extract_event ex.toadd ex.po ex.revisit pending in
          match a0 with
          | (Some e, ntoadd) -> begin
              let nadded = E.EventSet.add e ex.added in
              let newex = {ex with toadd = ntoadd; added = nadded;} in
              try match e with
                  | x when E.is_mem_store x -> visit_write newex cs e kont res
                  | x when E.is_mem_load x -> visit_read newex cs e kont res
                  | _ -> visit newex cs kont res
              with Not_found -> visit newex cs kont res
            end
          | None, _ ->
             let out = (clean_exec {ex with debug_rels =
                                              List.append ex.debug_rels
                                                [("rb", (E.EventRel.restrict_rel (fun x y -> x != y) (E.EventRel.sequence (E.EventRel.inverse ex.rf) ex.mo)))]}) in
             kont out res
        else res


    let finals ex =
      let out = E.EventSet.elements
                  (E.EventSet.filter
                     (fun x -> is_final_write x ex)
                     ex.added) in
      out

    let replace_events ex es =
      let find ev = E.EventSet.find
                      (fun x -> E.event_equal ev x)
                      es in
      let nadded = E.EventSet.map
                     (fun x -> find x)
                     ex.added in
      let nrf = E.EventRel.map
                  (fun (x, y) -> (find x, find y))
                  ex.rf in
      let nmo = E.EventRel.map
                  (fun (x, y) -> (find x, find y))
                  ex.mo in
      let npo = E.EventRel.map
                  (fun (x, y) -> (find x, find y))
                  ex.po in
      let ndebugrels = List.map
                         (fun (str, rel) -> (str, E.EventRel.map
                                              (fun (x, y) -> (find x, find y)) rel))
                         ex.debug_rels in
      {ex with added = nadded; rf = nrf; mo = nmo; po = npo; debug_rels = ndebugrels}


    let mykont test model_kont es cs = (fun e res ->
        let ncs = (List.append cs (make_cnstrnts e)) in
        M.solve_mem test es e.rfm ncs
          (fun es0 rfm0 cs0 res0 ->
            match cs0 with
            | [] ->
               if S.A.reject_mixed then M.check_sizes es0;
               if not (S.O.optace) || M.check_rfmap es0 rfm0
               then
                 let ne = replace_events e es0.M.S.E.events in
                 let pp_relns =
                   lazy begin
                       ("mo", ne.mo)::
                       ("hb", E.EventRel.remove_transitive_edges (hb ne))::
                       ("rf", ne.rf)::
                       ("po", ne.po)::
                       ("rmw", ne.rmws)::
(*                       ("revisit", E.EventSet.fold (fun ev rels -> E.EventRel.add (ev, ev) rels) ne.revisit E.EventRel.empty)::
                       ("rmw", ne.rmws)::
                       ("rs", rseq ne)::
                       ("sw", sw ne)::*)
                       ne.debug_rels
                     end in
                 let rfm = List.fold_left
                             (fun k w ->
                               M.S.RFMap.add (M.S.Final (M.get_loc w)) (M.S.Store w) k) rfm0 (finals ne) in
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

    let real e = fence e || E.is_mem e

    let check_rfms test rfms kfail kont model_kont res =
      let (_, cs0, es0) = rfms in
      let (es, rfm, cs) = solve test es0 cs0 in
      let rmws = M.make_atomic_load_store es in
      let evts = E.EventSet.filter real es.E.events in
      let inits = E.EventSet.filter E.is_mem_store_init evts in
      let po = U.po_iico es in
      let iico = U.iico es in
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
      let ex_init = {
          toadd = toadd;
          added = inits;
          po = (E.EventRel.union rmws po);
          iico = iico;
          mo = E.EventRel.empty;
          rf = E.EventRel.empty;
          revisit = E.EventSet.empty;
          safe = inits;
          exvals = (fun x -> false);
          rmws = rmws;
          rfm = rfm;
          flags = Flag.Set.empty;
          psc = E.EventRel.empty;
          debug_rels = []
        } in
      (visit ex_init cs (mykont test model_kont es cs) res)

    let check_event_structure test (rfms : (_ * S.M.VC.cnstrnts * S.event_structure) list) kfail kont model_kont  (res : 'a) =
      List.fold_left (fun re rf -> check_rfms test rf kfail kont model_kont re) res rfms
  end
