import YM.CF.Corne.Roar
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Corne
open Arena Tarn
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
section
variable (x:ℝ)(j r:ℕ)(Φ:Tab S→FileM c G)(A:Tab S→DirP c) {Z:Tab S}{a:Stores S}{i y:Site c}{p m L:ℕ}{M A' D' e u:ℝ}{k:ℕ}
lemma yPay(a:Stores S)(V:Config G c)(P:Tab S)(h:Wick Φ A L n σ C D)(p:C≥0)(hp:D≥0)(he:e≥0)(t:ℝ)(hu:0≤t) (H:∀ i:Site c, i ∉ a.dome (r*radiusB x)→∀ f,CakeF f i L n σ C → cFoot 2 (satX f)→ (∀ j, 2 ≤ j→ j ≤ 1→‖cake j (satX f)‖ ≤ 0)→ Allows n (f ∘ Vmove x V) 0 e)(Q:∀ i:Site c,i ∉ a.dome (j*radiusB x)→ Allows n (Φ P i ∘ Vmove x V) 0 t) (i:Site c): Allows n (issued x j r Φ A a P i ∘ Vmove x V) 0 (t+(plot L*e+ plot L*e)):=by -- fix binder
 let Y:= cClip x r A a P; let Z:= a.dome (r*radiusB x); let X:=a.dome (j*radiusB x)
 let p' := pavilion L i; let U:= Vmove x V; have hU(z y):Allows n (Y z y ∘ U) 0 e:=by
    unfold Y cClip; split
    next p=> exact H _ p.1 _ (h.vows P z y).1 (h.vows P z y).2.1 (h.vows P z y).2.2
    next p=> exact Jet.allows_const _ ((norm_zero).le.trans he)
 have he(i y:Site c)(hv:L < separation i y): Y i y=0:=by unfold Y cClip; split; exact not_not.mp fun u=> hv.not_ge (h.axis _ i y u); rfl
 have hZ : dict Y i=(∑ y∈p', Y y i) -(∑ y∈ p', Y i y):=by unfold dict; apply congrArg₂ (·-·); symm; apply sum_subset (subset_univ _); intro y _ hh; apply he; rw [separation_comm]; exact not_le.mp (mt (theatre ..).mpr hh); symm; exact Finset.sum_subset (subset_univ _) fun y _ hu=> he i y (not_le.mp (mt (theatre ..).mpr hu))
 let P'(V):ℂ:= if i∈X then 0 else Φ P i V
 have hp': Allows n (P' ∘ U) 0 t:=by
    by_cases h:i∈X; unfold P' Function.comp; simp only [if_pos h]; exact Jet.allows_const _ ((norm_zero).le.trans (by assumption)); unfold P' Function.comp; simp only [if_neg h]; exact Q _ h
 have hW:P' ∘ U + ((fun v=>∑ y∈p', (Y y i ∘ U) v)-(fun v=>∑ y∈p',(Y i y ∘ U) v))= issued x j r Φ A a P i ∘ Vmove x V:=by
    unfold issued; funext v; rw [Function.comp_apply, show cClip x r A a P=Y from rfl,hZ]; simp only [Pi.add_apply,Pi.sub_apply,Function.comp_apply,Finset.sum_apply, P', X,U]; split <;> rfl
 have hx: #(p')*e ≤ (plot L:ℝ)*e:= mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (pay_v _)) (by assumption)
 rw [← hW]; exact hp'.add (Newt.subtract_p ((summed (V:=fun y=> Y y i ∘ U) _ (fun y _=> hU y i)).mono hx) ((summed (V:=fun y=>Y i y ∘ U) _ (fun y _=>hU i y)).mono hx))
end

section
variable (x:ℝ)(j r:ℕ)(Φ:Tab S→FileM c G)(A:Tab S→DirP c) {Z:Tab S}{a:Stores S}{i y:Site c}{p m L:ℕ}{M A' D' e u:ℝ}{k:ℕ}
lemma viaW(hv:j ≤ r)(p:i∉ a.dome (L+r*radiusB x))(h:Wick Φ A L n σ C D): issued x j r Φ A a Z i= Φ Z i+dict (A Z) i:=by
 let V:=a.dome (r*radiusB x); have hp: i∉ V:=fun t=>p (farther (by omega) t); unfold issued; rw [if_neg (fun he=>hp (farther (Nat.mul_le_mul_right _ hv) he))]; apply congrArg (Φ Z i+·); unfold dict; refine congrArg₂ (·-·) (sum_congr rfl fun v _=> ?_) (sum_congr rfl fun v _=>?_)
 · unfold cClip; split; rfl; next he=> exact (not_not.mp (fun u=>he ⟨climb_W a.place p ((separation_comm ..).trans_le (h.axis Z v i u)),hp⟩)).symm
 unfold cClip; split; rfl; next he=> exact (not_not.mp (fun u=>he ⟨hp,climb_W a.place p (h.axis Z i v u)⟩)).symm
end
lemma beamW (j r n:ℕ)(σ:ℝ)(p:0<σ)(hy:3 ≤ n)(hr:2 ≤ j)(hk:j≤r):∃ s u:ℝ,0<s∧0<u∧∀ᶠ x in atTop,0≤ rankC s x ∧0≤ rankC u x ∧∀ {c f:Side}(S: StepData c f)(Φ:Tab S→FileM c G)(A:Tab S→DirP c)(m t:ℕ)(C D:ℝ), m ≤ (r-1)*radiusB x → t≤ (j-1)*radiusB x →(r+r+101)*radiusB x ≤ c.val →0≤C → 0≤ D → Wick Φ A m n σ C D →∀ (P:Tab S), (∀ i,CakeF (Φ P i) i t n σ C ∧ cFoot 2 (satX (Φ P i))) →∀ (M:Stores S)(V:Config G c), M.flags= RG.flags (temp x) V →∀ i:Site c, let E:= issued x j r Φ A M P i ∘ Vmove x V; let b:= composeCost n (vatP 1 1 n C 0 (rankC s x)) (1/2); let b':= composeCost n (vatP 1 1 n C 0 (rankC u x)) (1/2)
 Allows n E 0 (b+(plot m*b'+plot m*b'))∧ (i ∉ M.dome (m+r*radiusB x) → Allows n E 0 (compass n 2 x C D u)):=by
 let t:=min σ 1; have ht:0<t:= lt_min p zero_lt_one
 obtain ⟨s,v,H⟩:= trod (j-2) n t (by omega) ht (min_le_right ..); obtain ⟨c,w,H'⟩:= trod (r-2) n t (by omega) ht (min_le_right ..); refine ⟨s,c,v,w,?_⟩
 filter_upwards [H,H'] with x hs hz; obtain ⟨a,b,u,G0⟩:=hs; obtain ⟨a',b',u',G'⟩:=hz; refine ⟨b.le,b'.le ,?_⟩
 intro c' f S Φ A m t' C D g u K p' hD h P hP M V he i E bV bT
 have hQ :∀ i:Site c',i∉ M.dome (r*radiusB x)→ ∀ Q:SpaceX G c', CakeF Q i m n σ C → cFoot 2 (satX Q) → Allows n (Q ∘ Vmove x V) 0 bT:=fun i l Q k y=> G' S V M i (by rwa [show r-2+2=r from by omega]) he ((Nat.mul_le_mul_right _ (by omega)).trans K) Q 1 1 m C 0 (by omega) le_rfl (by rw [show r-2+1=r-1 by omega]; exact g) (Foot.change y (by decide) (by decide) le_rfl (k.under (min_le_left ..) le_rfl le_rfl)) -- tune
 constructor
 · refine yPay x j r Φ A M V P h p' hD ?_ bV ?_ (fun i l Q k a _=> hQ i l Q k a) (fun i l=> ?_ ) i
   · unfold bT vatP composeCost; have h:= b'.le; positivity
   · unfold bV vatP composeCost; have h:= b.le; positivity
   exact G0 S V M i (by rwa [show j-2+2=j from by omega]) he ((Nat.mul_le_mul_right _ (by omega)).trans K) (Φ P i) 1 1 t' C 0 (by omega) le_rfl (by rw [show j-2+1=j-1 by omega]; exact u) (Foot.change (hP i).2 (by decide) (by decide) le_rfl ((hP i).1.under (min_le_left ..) le_rfl le_rfl)) -- hmm ht.Fr order
 intro s'; unfold E; rw [viaW x j r Φ A hk s' h]; exact G' S V M i (by rw [show r-2+2=r by omega]; exact fun u=>s' (farther (by omega) u)) he ((Nat.mul_le_mul_right _ (by omega)).trans K) _ 2 2 m C D (by omega) le_rfl (by rw [show r-2+1=r-1 by omega]; exact g) ⟨((h.better P i).1).under (min_le_left ..) le_rfl le_rfl, (h.better P i).2⟩
end YM.CF.Corne
#print axioms YM.CF.Corne.capAX
#print axioms YM.CF.Corne.beamW
