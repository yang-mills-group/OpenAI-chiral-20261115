import YM.SU5.Registration.Momenta.Readable
/-!
 # Observable algebra in this reconstruction
 This Wightman field system (even/gauge symbols); working at polynomial test fields with
 the usual star charges. Not a C* net. Can include all Schwartz (even unbounded tsupport)
 with indicated containment; obtains local algebras on bounded/open sets in particular.
 Doesn't assert completeness of this list of generators for recognizing actual or other
 SU(5) questions beyond those reading here. Need estimates on a useful family V.
 Adapts `YM/SU5/FiniteGaugeData/Cirrus/Scepter,Saffron`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed.Carton
open Function Set Filter MeasureTheory Measure Complex Submodule SatinRegistration
open Boundary Probe Mink Mink.Poincare Multiplier Roy Spectral OS.Semigroup SatinEdge.RealSheet
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace ComplexOrder
variable {H:Hilbert}{S: _root_.YM.OS.Semigroup H timeAxis}{V:Type*}[AddCommGroup V][Module ℂ V]
variable (B:Carton S V)(J:JMap V)(u:Remembers B J)
local notation "D"=> radial S
local notation "G"=> bands S
local notation "R"=> B.station
local notation "L"=> B.joinT
local notation "F'"=> B.pointGrade
local notation "ε"=> B.citizen
open WView Palette
variable {F:InkWaves V}{W:WView V}(g:InkPort B F W)(K:Courts V)(m:K.Carriage F){n:ℕ}
abbrev display : Type := Module.End ℂ (B.citizen)
def lettersO (T:Set E4): Set (MarkType V):= {p|tsupport p.2⊆T}
noncomputable def county (T:Set E4): Subalgebra ℂ B.display:= Algebra.adjoin ℂ ((fun i:MarkType V=> B.pointMap i.1 i.2) '' lettersO T)
local notation "Λ" T:max=> B.county T
local notation "E"=> B.display
variable (T:Set E4)
lemma portrayed (p:MarkType V)(e:tsupport p.2 ⊆ T): B.pointMap p.1 p.2 ∈ B.county T:= Algebra.subset_adjoin ⟨p,e,rfl⟩
lemma passportMark (p:MarkWords V) (h: ∀ i∈p,tsupport i.2⊆T): B.voice p ∈ B.county T:=by
 induction p with
 | nil=> exact (Λ T).one_mem
 | cons i p ih=> exact (Λ T).mul_mem (B.portrayed T i (h i List.mem_cons_self)) (ih (fun j p' => h _ (List.mem_cons_of_mem _ p')))
lemma isotone {T U:Set E4}(e:T⊆U) : B.county T≤ B.county U:= Algebra.adjoin_mono (image_mono (show lettersO (V:=V) T ⊆ lettersO U from fun _ h=> Subset.trans h e)) -- syntax
lemma regional_support (x:Poincare)(f:Test4): tsupport (Joint.push x f) ⊆ x.sends '' tsupport f:=by
 let g:= Poincare.sends x⁻¹; have h:Continuous g:=by unfold g Poincare.sends; fun_prop
 have p: MapsTo g (tsupport (Joint.push x f)) (tsupport f):= MapsTo.closure (s:=Function.support (Joint.push x f)) (t:=Function.support f) (fun u p'=> fun t=> p' ((Joint.push_at x f u).trans t)) h
 exact fun v t=> ⟨g v,p t,Poincare.emerges x v⟩
def Separates (U T:Set E4):Prop:= ∀ x∈U,∀ y∈T,x-y ∈ Mink.spacelike
variable (U:Boundary.Action B.station)(h:B.Joins K U)
noncomputable abbrev seenBy (p:Poincare)(x:E): E:= ((B.liftV K U h p)*(x))*(B.liftV K U h p⁻¹)
local notation "Θ"=> B.seenBy K U h
include g m u
lemma counties_commute (T': Set E4) (e:Separates T T') (A D':E)(p:A∈ Λ T)(q:D'∈ Λ T'): Commute A D':=by
 refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute q ?_; rintro _ ⟨x,t,rfl⟩; apply Commute.symm; apply Algebra.commute_of_mem_adjoin_of_forall_mem_commute p; rintro _ ⟨y,v,rfl⟩; exact (B.supported J g u (WView.isLocal g m) y.1 x.1 y.2 x.2 (fun i h j k=> e _ (v h) _ (t k))).symm
omit g m u
include h
abbrev angle (p:Poincare) : E:= B.liftV K U h p
lemma angle_comp (x y:Poincare): B.angle K U h x * B.angle K U h y=B.angle K U h (x*y):= by ext1 z; apply Subtype.ext; exact DFunLike.congr_fun (U.mult x y).symm z.val
lemma angle_0 : B.angle K U h 1 = 1:= by ext1 z; apply Subtype.ext; exact DFunLike.congr_fun U.one z.val
lemma roots_time (x:Poincare): B.angle K U h x * B.angle K U h x⁻¹= 1:= by rw [B.angle_comp,mul_inv_cancel,B.angle_0]
lemma roots_back (x:Poincare): B.angle K U h x⁻¹ * B.angle K U h x= 1:=by rw [B.angle_comp,inv_mul_cancel,B.angle_0]
lemma fence (x:Poincare) (A:E) : Θ x⁻¹ (Θ x A)=A:=by
 unfold seenBy; rw [inv_inv, ←mul_assoc,←mul_assoc, B.roots_back,one_mul,mul_assoc, B.roots_back,mul_one] -- `angle` defeq
lemma counties_fly (p:Poincare)(A:E)(q:A∈ Λ T): Θ p A∈Λ (p.sends '' T):=by
 let W':= Λ (p.sends '' T); let P:=B.angle K U h p; let P':= B.angle K U h p⁻¹; refine Algebra.adjoin_induction (p:=fun x _=> Θ p x ∈W') ?_ ?_ ?_ ?_ q
 · rintro _ ⟨⟨x,f⟩,g,rfl⟩; change P* B.pointMap x f *P'∈W'; rw [show P*B.pointMap x f=_ from (show P* (B.pointMap x f)=(B.pointMap (K.mi p.Λ x) (Joint.push p f))*P from B.fields_covariant K U h p x f), mul_assoc, B.roots_time, mul_one]; exact B.portrayed _ (K.mi p.Λ x,_) ((regional_support p f).trans (image_mono g))
 · intro r; rw [seenBy,Algebra.algebraMap_eq_smul_one,Algebra.mul_smul_comm, Algebra.smul_mul_assoc,mul_one, B.roots_time]; exact W'.smul_mem W'.one_mem r
 · intro i j p q h₁ h₂; change P*(i+j)*P'∈ _; rw [mul_add,add_mul]; exact W'.add_mem h₁ h₂
 intro i j _ _ hi hj; let e:= B.roots_back K U h p; have he: Θ p (i*j)=Θ p i*Θ p j:=by
   change P*(i*j)*P'=P*i*P'*(P*j*P'); nth_rw 1 [show i*j=i*1*j by rw [mul_one],← e]; change P*(i*(P'*P)*j)*P'=P*i*P'*(P*j*P'); simp only [mul_assoc]
 rw [he]; exact W'.mul_mem hi hj
lemma counties_moved (p:Poincare)(A:B.display): A∈ Λ T ↔ Θ p A ∈ Λ (p.sends '' T):=by
 refine ⟨B.counties_fly K _ U h p A,fun v=>?_⟩; have e:=B.counties_fly K (p.sends '' T) U h p⁻¹ (Θ p A) v; rw [B.fence] at e; exact B.isotone (image_subset_iff.mpr (by rintro _ ⟨x,p,rfl⟩; rw [mem_preimage, Poincare.unmade]; exact p)) e
omit h
def relations (A C:B.display):Prop:=∀ x y:B.citizen, inner ℂ (A x).val y.val=inner ℂ x.val (C y).val
variable {C C' A A' : B.display}
local notation "Ω"=> (B.relations)
lemma paired_one : B.relations 1 1:= fun _ _=> rfl
lemma paired_two (p:Ω A C) : Ω C A:=fun x y=>by rw [← inner_conj_symm, ← inner_conj_symm (x.val),p y x]
lemma paired_add (p:Ω A C)(q:Ω A' C') : Ω (A+A') (C+C'):=fun x y=>by simp only [LinearMap.add_apply,Submodule.coe_add,inner_add_left,inner_add_right,p x y,q x y]
lemma paired_mul (p:Ω A C)(q:Ω A' C') : Ω (A*A') (C'*C):=fun x y=> (p (A' x) y).trans (q x (C y))
lemma paired_smul (p:Ω A C)(c:ℂ): Ω (c•A) (star c • C):=by
 intro x y; simp only [LinearMap.smul_apply,Submodule.coe_smul_of_tower,inner_smul_left,inner_smul_right]; rw [p x y]; rfl
lemma paired_determines (p:Ω A C)(q:Ω A C'): C=C':= by ext1 x; apply Subtype.ext; exact (B.charged_iff).2 (fun i=> (p (B.evaluate i) x).symm.trans (q (B.evaluate i) x))
-- Every local algebra element (indeed everywhere) adjoint yields unique star on this domain.
-- Don't need to install typeclass -- use `pair_local`.
include u
lemma paired_local (A:B.display)(p:A∈ Λ T) : ∃ C∈ Λ T, B.relations A C:=by
 apply Algebra.adjoin_induction (p:=fun x _=>∃ C∈Λ T, B.relations x C) _ _ _ _ p
 · rintro _ ⟨⟨x,f⟩,e,rfl⟩; refine ⟨B.pointMap (J x) (Probe.bar f),B.portrayed T (opTag J (x,f)) ((SatinRegistration.bar_reach f).le.trans e),fun i j=> B.FormalSharp J u (x,f) i j⟩
 · intro x; rw [Algebra.algebraMap_eq_smul_one]; exact ⟨star x • 1, (Λ T).smul_mem (Λ T).one_mem _, B.paired_smul B.paired_one x⟩
 · rintro i j _ _ ⟨C,p,h⟩ ⟨C',q,u⟩; exact ⟨C+C',(Λ T).add_mem p q,B.paired_add h u⟩
 rintro i j _ _ ⟨C,p,h⟩ ⟨C',q,u⟩; exact ⟨C'*C,(Λ T).mul_mem q p,B.paired_mul h u⟩
omit u
def navigate(x:B.display): B.station →ₗ.[ℂ] B.station:= ⟨ε,(ε).subtype.comp x⟩
lemma navigated (e:Ω A C) : B.navigate C ≤ (B.navigate A).adjoint:= LinearPMap.IsFormalAdjoint.le_adjoint B.populous e
lemma vetted (e:Ω A C): (B.navigate A).IsClosable:= (LinearPMap.adjoint_isClosed B.populous).isClosable.leIsClosable (B.navigated (B.paired_two e))
end YM.SatinWFixed.Carton
