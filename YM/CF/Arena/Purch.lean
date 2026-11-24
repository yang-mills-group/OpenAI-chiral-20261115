import YM.CF.Arena.Bloc
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Arena
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
variable {K:Teller G}
section
variable(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E]
structure Tight (p k l:ℕ)(f:E→ℂ)(x:E)(A C:ℝ)(s:ℝ):Prop where
 uses(u:E)(h:‖u-x‖<s): Allows l f u A
 hush: cFoot p f -- center fixed 0!
 cap(j:ℕ)(v:p ≤ j)(hp:j ≤ k): ‖cake j f‖ ≤ C
end
abbrev hoop(S:StepData c f)(s:Signed)(p:Site c):= univ.filter (fun i: Along S=> herald S s i=p)
def heed (T:Tube G S)(P:Tab S)(q:Chi)(x d:ℝ)(l:ℕ)(s:Signed)(p:Site c): SpaceX G c:=∑ i∈ hoop S s p,bale T P q x d l s i
def fame (T:Tube G S)(P:Tab S)(q:Chi)(x d:ℝ)(l:ℕ):FileM c G:=fun p=> ((Fintype.card Signed:ℂ)⁻¹) • (∑ s,heed T P q x d l s p)
section
variable {o:Site c}{L:ℕ}{A H V W:ℝ}
lemma hoop_c (S:StepData c f)(s:Signed)(p:Site c): (hoop S s p).card ≤ about S.patch.L 0:=by
 apply le_trans (card_le_card (show hoop S s p ⊆ peakM S s p 0 from ?_)) (num_peak ..); intro i h; exact mem_filter.mpr ⟨mem_univ _,((mem_filter.mp h).2) ▸ (separation_self _).le⟩
def Urge (F:SpaceX G c)(o:Site c)(q k l n:ℕ)(σ A B:ℝ):Prop:= CakeF F o l n σ A∧ cFoot q (satX F) ∧ ∀ i,q ≤ i → i ≤ k → ‖cake i (satX F)‖ ≤ B
variable{p p':SpaceX G c}{j mN:ℕ}
lemma Urge.under(h:Urge p o j mN l n σ A V)(hp:A ≤ C)(hv:V ≤ W)(hk:l ≤ L): Urge p o j mN L n σ C W:=⟨h.1.under le_rfl hk hp,h.2.1,fun i a b=> (h.2.2 i a b).trans hv⟩
lemma urge_add(p q:SpaceX G c)(h:Urge p o j mN l n σ A V)(v:Urge q o j mN l n σ C W)(hp:0<σ)(hg:j ≤ n)(hv:mN ≤ n): Urge (p+q) o j mN l n σ (A+C) (V+W):=by
 have he:‖(0:InputZ G c)‖<σ:=by simpa using hp
 refine ⟨h.1.add v.1,merger h.2.1 v.2.1 le_rfl (((h.1.ledger _ he).order hg).smooth) (((v.1.ledger _ he).order hg).smooth),fun i u t=>?_⟩
 apply (le_trans ?_ (add_le_add (h.2.2 i u t) (v.2.2 i u t))); unfold cake; rw [show satX (p+q)=satX p+satX q from rfl,iteratedFDeriv_add_apply (((h.1.ledger _ he).order (t.trans hv)).smooth) (((v.1.ledger _ he).order (t.trans hv)).smooth),smul_add]; exact norm_add_le ..
lemma urgeSum{ι:Type}(Q:Finset ι){f:ι→SpaceX G c}(h:∀ i∈Q, Urge (f i) o j mN l n σ A V)(hp:0<σ)(hg:j ≤ n)(hv:mN ≤ n): Urge (∑ i∈Q, f i) o j mN l n σ (Q.card*A) (Q.card*V):=by
 induction Q using Finset.induction with
 | empty=> simp only [sum_empty,card_empty,Nat.cast_zero,zero_mul]; exact ⟨CakeF.zeroP le_rfl,hatZ,fun i p q=>by unfold cake; change ‖(i.factorial:ℝ)⁻¹ • iteratedFDeriv ℝ i (fun _ :InputZ G c=>(0:ℂ)) 0‖ ≤ 0; rw [iteratedFDeriv_fun_zero]; simp⟩
 | @insert i Q he ih=>rw [sum_insert he,card_insert_of_notMem he,Nat.cast_add,Nat.cast_one]; exact (urge_add _ _ (h i (by simp)) (ih (fun i v=>h i (by simp [v]))) hp hg hv).under (by ring_nf; rfl) (by ring_nf; rfl) le_rfl
lemma Urge.change(h:Urge p o j mN l n σ A V)(hx:0<σ)(hg:j ≤n)(hp:mN ≤ n)(t:ℂ): Urge (t • p) o j mN l n σ (‖t‖*A) (‖t‖*V):=by
 have hv:= h.1.ledger 0 (by simpa using hx); let P:= satX p; let T:ℂ→L[ℝ]ℂ:= ContinuousLinearMap.lsmul ℝ ℂ t; have he: ‖T‖≤‖t‖:=ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun i=> (norm_mul ..).le; have hh:satX (t•p)= T ∘ P:=rfl
 have heX(k)(hp:k ≤ n): iteratedFDeriv ℝ k (satX (t • p)) 0= T.compContinuousMultilinearMap (iteratedFDeriv ℝ k P 0):=by rw [hh,T.iteratedFDeriv_comp_left (show ContDiffAt ℝ (n:ℕ∞ω) P 0 from hv.smooth) (by exact_mod_cast hp)]
 refine ⟨h.1.pay t,fun i hi=>?_,fun i p v=> ?_⟩
 · rw [heX i (hi.le.trans hg),show iteratedFDeriv ℝ i P 0=0 from h.2.1 i hi]; ext; simp
 unfold cake; rw [heX i (v.trans hp),show (i.factorial:ℝ)⁻¹ • T.compContinuousMultilinearMap _= T.compContinuousMultilinearMap (cake i P) from by ext; exact (map_smul T ((i.factorial:ℝ)⁻¹) _).symm]; exact (ContinuousLinearMap.norm_compContinuousMultilinearMap_le ..).trans (mul_le_mul he (h.2.2 i p v) (norm_nonneg _) (norm_nonneg _))
lemma fame_p(h:∀ i s, Urge (bale T P q x d l s i) (herald S s i) j mN L n σ A V)(hx:0<σ)(hg:j ≤n)(hp:mN ≤ n)(hA:0 ≤ A)(hV:0 ≤ V): let p:= about S.patch.L 0; Urge (fame T P q x d l o) o j mN L n σ (p*A) (p*V):=by
 intro p; have he(s:Signed): Urge (heed T P q x d l s o) o j mN L n σ (p*A) (p*V):= (urgeSum (hoop S s o) (fun i v=> (show herald S s i=o from (mem_filter.mp v).2) ▸ h i s) hx hg hp).under (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hoop_c S s o)) hA) (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hoop_c S s o)) hV) le_rfl
 let i:= (Fintype.card Signed:ℂ); have hp: ‖i⁻¹‖ * ((univ:Finset Signed).card * (p:ℝ)) = (p:ℝ):=by unfold i; rw [norm_inv]; simp
 have ht(y:ℝ): ‖i⁻¹‖ * ((univ:Finset Signed).card * ((p:ℝ)*y))=p*y:= by rw [←mul_assoc _ _ y,←mul_assoc _ _ y,hp]
 exact ((urgeSum (univ:Finset Signed) (fun s _=> he s) hx hg (by assumption : mN ≤ n)).change hx hg (by assumption : mN ≤ n) i⁻¹).under (ht _).le (ht _).le le_rfl
end
end YM.CF.Arena
