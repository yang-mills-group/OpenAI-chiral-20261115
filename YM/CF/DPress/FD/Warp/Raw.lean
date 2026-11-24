import YM.CF.DPress.FD.Warp.Rent
/-! Full random Basic map construction. FD in Vision (rectangle joint law
 on the finite orientation-jitter/color-memory implementation). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Cash Bifold Deck Hue Geo Warm Frame Ramp Spire Skye SU Lat Scroll Tw Finset Con Row Wilson
open Cube (More assembly)
open scoped Topology BigOperators ENNReal NNReal Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {n:Side}{r l m N:ℕ}{u t:ℝ}
-- Consultation radius = dependence range of vision. Basic map deterministic on choice c.
structure Scout (I:Type)[Fintype I](n:Side)(u t:ℝ)(R:ℕ) where
 V:Vision (More n) R I
 X:I→Pane n→Pane n
 basicF : ∀ i, Basic n (X i) u t R
 V_ear : ∀ e U,V.idT (fun i=> X i U e) (Skye.win R e)
 V_move : Sweep n→Equiv.Perm I
 sgP :∀ s, Chooses V.c (V_move s)
 sym : ∀ s i U,flashA s (X i U)= X (V_move s i) (flashA s U)
namespace Turf
-- rate plaque through all-size frames
lemma sail_W {F:Seat n→ rug n}{U:Pane n}{u:ℝ}(p:∀ i:reach n,dist (sail (F i.1) (U i)) (F (fromE i).2)≤u)(w:Lattice.Walk)(x:Seat n):dist (sail (F x) (travel U x w)) (F (Lattice.stop x w)) ≤ w.length*u:=by
 induction w generalizing x with
 | nil=> simp [travel,Frame.sail_id,Lattice.stop]
 | cons i w ih=>
    let y:=x+i.vec; have hx: dist (sail (F x) (i.read U x)) (F y) ≤ u:=by
        rcases i with ⟨i,u|u⟩; exact p (x,i)
        let z:=x-step i; change dist (sail (F x) (negDir i|>.read U x)) _ ≤ _; rw [Step.neg_read,dist_duo,inv_inv]; have hp:y=z:=by unfold y z; simp [Step.vec,sub_eq_add_neg]; -- ok
        rw [hp]; convert p (z,i) using 1; rw [fromE]; dsimp; unfold z; rw [sub_add_cancel] -- tune
    let z:=travel U y w; have hz:dist (sail (F y) z) (F (stop y w))≤ w.length*u:=ih y; refine le_trans (Eq.trans_le (show dist (sail (F x) _) _ = dist (sail (sail (F x) (i.read U x)) z) (F (stop y w)) from (by rw [sail_mul]; rfl)) (dist_triangle _ (sail (F y) z) _)) ((add_le_add ((Frame.sail_L ..).trans_le hx) hz).trans_eq ?_); simp; ring
lemma broad_L (F:Seat n→ rug n)(X:Pane n) (z:ℝ)(u:ℝ)(p:∀ i:reach n,dist (sail (F i.1) (X i)) (F (fromE i).2)≤u)(h:4*u ≤ group.colorScale*z)(v:∀ i,F i∈ Frame _): RG.flags z X=∅:=by
 apply Skye.broad; intro i; let Y:=faceValue X i; have ht: dist (sail (F i.1) Y) (F i.1)≤ 4*u:=by simpa only [Y,faceValue,square_stop,show (square i.2.val.1 i.2.val.2).length=4 from rfl,Nat.cast_ofNat] using sail_W p (square i.2.val.1 i.2.val.2) i.1
 apply (mul_le_mul_iff_right₀ group.colorScale_pos).mp; change group.colorScale * group.chord Y ≤ group.colorScale*z; rw [←BPress.chord.one,← Con.metricB,← Frame.sail_R (v i.1),Frame.sail_id]; exact ht.trans h
lemma scoutP {I:Type}[Fintype I]{V:Vision (More n) r I}(U:Plan V l m){T:Trophy n l u}{a:ℝ}(P:Leader T m 5 a)(t':1<(More n).val)(h:baseP≤a)(v:0<u)(p:0<l)(z:0<m)(κ:Treasure l m u)(D:ℕ)(w: Track l ≤ D)(x:r≤D)(E:4*(rate a/(m:ℝ)) ≤ group.colorScale*t): Nonempty (Scout (I×Cotton n) n u t D):=by
 let Q:Valve n (rate a/(m:ℝ)):= vents.some; let X(i:I×Cotton n)(A:Pane n):= flow U P Q i.1 i.2 A; let V':= V.pair (Salar n r); let g(i:Sweep n):= Equiv.prodCongr (moveK U i) (act i)
 refine ⟨{V:=V'.rearm x, X:=X, basicF:=fun ⟨i,c⟩=>?_, V_ear:=fun e X=> ?_, V_move:=g, sgP:=?_, sym:=fun s i X=>(flow_K U P Q _ _ _ t' s).symm}⟩
 · refine ⟨fun X=> broad_L (realF U P i c X) _ t _ (flow_est U P Q i c X z h p v.le κ) E (fun t=>real_ve U P i c X t z),flow_M ..,fun X e=>flow_i U P Q i c X w,fun X Z j u=>entry_h U P Q i c c X w u z (fun i _=>rfl) (fun i _ _=>rfl) ⟩ -- flow_i dependent implicit e binder.
 · exact pay_Y U P Q X w x z -- name tune
 intro i s; apply congrArg₂ (·*·) (U.ward i.s _ _) (w_t (r:=r) i s.2) -- tune
-- purchase $Guard and threshold.H.Radius before size.
lemma scale_S(p:0<t)(w:ℝ)(h:0<w) : ∃ d N:ℕ,∃ u:ℝ,0<u ∧ u≤ w ∧ ∀ n:Side,N<(More n).val→∃ (I:Type)(_:Fintype I), Nonempty (Scout I n u t d):=by
 obtain ⟨a,u,P⟩:=bookF 5 le_rfl; obtain ⟨l,L⟩:∃ l,Geo.RatioT l:=by obtain ⟨l,h⟩:=Geo.earn; exact ⟨l+1,h _ (by omega)⟩ -- complex numeral κ.
 obtain ⟨m,hm⟩:= exists_nat_gt (4*rate a/(group.colorScale*t)); have he:0< group.colorScale*t:=mul_pos group.colorScale_pos p
 have ht:0≤ a:= base_p.trans u; have hz:0<(m:ℝ):= lt_of_le_of_lt (by unfold rate; positivity) hm; have hm':0<m:=by exact_mod_cast hz
 let v:=l*m; have hp:0<v:= Nat.mul_pos L.1 hm'; obtain ⟨d,hd,hd',t'⟩:= treasure_earned v hm' h; obtain ⟨r,N,hk⟩:=Proto L hm';
 refine ⟨max (Track v) r,max (2*(globe v+1)) (max 1 N),d,hd,hd',?_⟩; intro n e; obtain ⟨I,inst,F,k⟩:= hk (More n) (by omega); obtain ⟨k⟩:=k; obtain ⟨T⟩:= Con.cabinet hd.le (n:=n) (l:=v) (by omega); obtain ⟨X⟩:= P n v _ _ T hm' hd.le t'; refine ⟨I×Cotton n,inferInstance,scoutP k X (by omega) u hd hp hm' t' _ (le_max_left ..) (le_max_right ..) ?_⟩
 rw [← mul_div_assoc]; apply (div_le_iff₀ hz).2; exact ((div_lt_iff₀ he).1 hm).le.trans_eq (mul_comm ..)
end Turf
end YM.CF.DPress.FD
