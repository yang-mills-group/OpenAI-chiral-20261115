import YM.CF.BProof.Law.Cloud
import YM.CF.BProof.Angular.Tape

/-! Change of variables formula proving **exact** law after drawing Mark densities.
Normalized probability for full iid cloud; label eligibility and its geometry independent
of the noise. Drawing t-dependent additional Fock integrand terms via arbitrary real or
complex stopped test after the setup trace. Formula for each term. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Angular.Yard
open Function Lattice Gauge CF.BProof.Face SU MeasureTheory Wilson Finset Filter Law RG
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
local notation "G" => SU.group
variable {E':Type}[NormedAddCommGroup E'][NormedSpace ℝ E'][MeasurableSpace E'][BorelSpace E'][SecondCountableTopology E'][CompleteSpace E']
variable {s: Side}(Y:Yard s)(y:ℝ)(S:Hall s)(U W:Config G s)(t:Y.FaceS)

/-- recombining: touches all rent; squashes forest; field, for gap horizontals, from U. -/
def mix : Config G s:= Y.squash (patch Y.rent W U)
def view := Y.centers y S U t
def play (w:Config G s) : Config G s := Y.mix U (Y.view y S U t*w)
lemma mix_rent {p:Bond s} (h:p∈Y.rent) : Y.mix U W p=W p:=by
 obtain ⟨i,hi⟩:=(Y.rents).1 h; unfold mix squash patch; rw [if_neg (Y.leased i hi),if_pos h]
lemma mix_field : Set.EqOn (Y.mix U W) U ↑Y.field:=fun p hp=>by unfold mix squash patch; replace hp:=not_or.mp (show ¬(p∈Y.trunks∨p∈Y.rent) from fun h=>mem_compl.mp (Finset.mem_coe.mp hp) (mem_union.mpr h)); rw [if_neg hp.1,if_neg hp.2]
lemma played (k:Y.Index){p:Bond s}(h:p∈Y.leases k) : Y.play y S U t W p=Y.slot k y S U t p*W p:=by unfold play; rw [mix_rent Y _ _ (Y.rents.mpr ⟨k,h⟩),Pi.mul_apply]; unfold view centers; rw [Y.rents_root k p h]
lemma play_m : Measurable (fun p : (Config G s × Y.FaceS) × Config G s=>Y.play y S p.1.1 p.1.2 p.2):=by
 let q:=(Function.uncurry (Y.centers y S)) ∘ Prod.fst (α:=(Config G s × Y.FaceS)) (β:=Config G s); have h:Measurable q:= (Y.centers_m y S).comp measurable_fst
 unfold play mix; apply (Y.squash_c).comp (f:=fun (p : (Config G s × Y.FaceS) × Config G s)=> patch Y.rent (q p * p.2) p.1.1) -- tune
 exact (patch_m (B:=SU.group.El) Y.rent).comp ((h.mul measurable_snd).prodMk (measurable_fst.comp measurable_fst))
lemma from_ball : Y.owed y S (Y.play y S U t W) t= ∏ p∈Y.rent,density G (xi y) 1 (W p):=by
 rw [price Y _ S (Y.play y S U t W) t (Y.squash_flat _)]; refine prod_congr rfl fun p hp=>?_; rw [Y.centers_eq y S (Y.play y S U t W) t U (Y.mix_field ..)]; unfold play; rw [mix_rent Y U _ hp,Pi.mul_apply]; change density G (xi y) (Y.view y S U t p) (_*_) = _; simp only [density_apply,cd]; group -- tune
lemma ticks (V:Config G s)(h:Set.EqOn W V ↑Y.rent): Y.play y S U t W=Y.play y S U t V:=by
 unfold play mix; congr 1; ext1 p; unfold patch; split; rename_i hp; simp only [Pi.mul_apply,h hp]; exact rfl
abbrev selected (p:Y.Glyph)(F:Config G s→ Y.FaceS → E')(U:Config G s) := if Y.accepted y S U p then F U (Y.sweepLabel y S U p) else 0
lemma select_pay (p:Y.Glyph)(F:Config G s→ Y.FaceS → E')(hp:Envelope (Function.uncurry F)): Envelope (Y.selected y S p F):=by
 obtain ⟨C,H⟩:=hp.cost; refine ⟨Measurable.ite (accepted_m Y y S p) (hp.meas.comp (measurable_id.prodMk (Y.sweepLabel_m y S p))) measurable_const,C,fun x=> ?_⟩; unfold selected; split; exact H (x,Y.sweepLabel y S x p); rw [norm_zero]; exact le_trans (norm_nonneg _) (H (x,1))

 
def selcost (F : Config G s→Y.FaceS→E') (x) (u) := Y.owed y S x u • F x u
lemma selcost_ep (F: Config G s→Y.FaceS→ E') (hp:Envelope (Function.uncurry F))(hx:xi y≤1): Envelope (Function.uncurry (Y.selcost y S F)):=by
 have ht:= Y.owed_env y S hx; obtain ⟨C,H⟩:=ht.cost; obtain ⟨D,L⟩:=hp.cost; exact ⟨ht.meas.smul hp.meas,C*D,fun x=> (norm_smul ..).trans_le (mul_le_mul (H x) (L x) (norm_nonneg _) ((norm_nonneg _).trans (H x)))⟩

lemma mix_pay (p:Y.Glyph)(F:Config G s→Y.FaceS→E')(V:Config G s)(h: Envelope (Function.uncurry F))(hx:xi y≤1):
    (∫ U,Y.selected y S p (Y.selcost y S F) (Y.mix V U) ∂prior G s)=
    if Y.accepted y S V p then (∫ W,F (Y.play y S V (Y.sweepLabel y S V p) W) (Y.sweepLabel y S V p) ∂Measure.pi fun _:Bond s=> cloud G (xi y)) else 0:=by
 let Q:=Y.sweepLabel y S V p; let P:=Y.play y S V Q
 have hg(U:Config G s):=Y.accepted_eq y S (Y.mix V U) (W:=V) (Y.mix_field V U) p; have ht(U:Config G s): Y.sweepLabel y S (Y.mix V U) p=Q:=Y.sweepLabel_eq y S _ (Y.mix_field V U) p
 unfold selected; simp_rw [hg]; split_ifs; swap; · simp
 have hv:Measurable P:=(Y.play_m y S).comp (f:=fun w:Config G s=> ((V,Q),w)) (by fun_prop)
 simp_rw [ht]; let t:=Y.view y S V Q; let f(U:Config G s):= Y.selcost y S F (Y.mix V U) Q; change (∫ U,f U ∂prior G s)=∫ W,F (P W) Q ∂Measure.pi _
 have hh:MeasurePreserving (fun U:Config G s=>t*U) (prior G s) (prior G s):= measurePreserving_pi _ _ (f:=fun i u=> t i*u) (fun i=> measurePreserving_mul_left group.probHaar (t i))
 have hx'(w): f (t*w)=(∏ p∈Y.rent,density G (xi y) 1 (w p)) • F (P w) Q:=by
   change Y.owed y S (Y.play y S V Q w) Q • _ = _; rw [from_ball]; rfl
 have hf:Measurable f:= by
   let K(U:Config G s):=(Y.mix V U,Q)
   have heh : Measurable (fun U:Config G s=>patch Y.rent U V) := (patch_m (B:=SU.group.El) Y.rent).comp (f:=fun U:Config G s=>(U,V)) (by fun_prop)
   have hg: Measurable (Y.mix V):= (Y.squash_c).comp heh; change Measurable (Function.uncurry (Y.selcost y S F) ∘ K); exact (Y.selcost_ep y S F h hx).meas.comp (f:=K) (hg.prodMk (measurable_const (a:=Q)))
 rw [← apply_pres hh hf, cloud_w_part G (xi y) (coin_pos ..) hx Y.rent]; simp_rw [hx']; rfl
 · exact Law.pull h (q:=fun w=>(P w,Q)) (hv.prodMk measurable_const)
 exact fun x y h=> congrArg (fun t=>F t Q) (ticks _ _ S V x Q y h)

/-- after squashing and summing all accepted signs (on flat gap ends), this formula
per summand integrates the ball densities by playback. -/
lemma replay (p:Y.Glyph)(F : Config G s→ Y.FaceS → E')(h:Envelope (Function.uncurry F))(hx:xi y≤1) :
    (∫ U,Y.selected y S p (Y.selcost y S F) (Y.squash U) ∂prior G s) = ∫ V, if Y.accepted y S V p then (∫ W,F (Y.play y S V (Y.sweepLabel y S V p) W) (Y.sweepLabel y S V p) ∂Measure.pi fun _:Bond s=>cloud G (xi y)) else 0 ∂prior G s := by
 let f(U:Config G s):= Y.selected y S p (Y.selcost y S F) (Y.squash U)
 have hf:Envelope f:= Law.pull (select_pay Y y S p _ (Y.selcost_ep y S F h hx)) Y.squash_c
 simp_rw [← mix_pay Y y S p F _ h hx]
 change (∫ U,f U ∂ Measure.pi fun _:Bond s=>group.probHaar)= ∫ W, ∫ U,f (patch Y.rent U W) ∂prior G s ∂prior G s
 have ht (U W:Config G s): patch Y.rent U W=patch Y.rentᶜ W U := by ext1 p; unfold patch; by_cases v:p∈Y.rent <;> simp [v]
 simp_rw [ht]; exact Law.refresh Y.rentᶜ (fun _=> group.probHaar) hf
end YM.CF.BProof.Angular.Yard
