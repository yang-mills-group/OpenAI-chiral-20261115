import YM.SU5.SatinWard.Resolution.Symbol
import YM.SU5.Silk.Clock.Face

/-!
# Pseudoscalar clover FF shapes
-/
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.QuadClock
open Neon
open Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew
variable {N n B:Side}
open Tap Waxy Ione.Clock StressFlux SU
-- adapters using localFace (..Silk.Clock.Face,Crush)
def pegW(i j:PlaqAxes)(x:ℂ):Skate:= fun u v=> if i=u ∧ j=v then x else 0
def coupleW(i j:PlaqAxes) (x:ℂ):Skate:=pegW i j x+pegW j i x
abbrev Ω₁:=coupleW lowLow highHigh Complex.I
abbrev Ω₂:=coupleW rimB rimC Complex.I - coupleW rimA rimD Complex.I

def PEven(A:Skate):Prop:= ∀ p:Signed,p∈ Loomed → localFace p A=A

lemma couple_Verc (i j:PlaqAxes)(x:ℂ):Verc (coupleW i j x):= by
 have he(i j v w:PlaqAxes):pegW i j x v w=pegW j i x w v:=by simp [pegW,and_comm]
 intro v w; unfold coupleW; simp only [Pi.add_apply]; rw [he i j v w,he j i v w,add_comm]; -- tune

lemma peg_follow(s:Signed)(i j:PlaqAxes)(x:ℂ): localFace s (pegW i j x)=pegW (move s i) (move s j) ((levy s i*levy s j) • (Pec.pays s x)):=by
 funext a b; obtain ⟨a,rfl⟩:=(move s).surjective a; obtain ⟨b,rfl⟩:=(move s).surjective b; rw [face_p]; by_cases p:i=a<;>by_cases q:j=b<;>simp [pegW,p,q]
lemma local_plus(s:Signed)(f g:Skate):localFace s (f+g)=localFace s f+localFace s g:=by funext a b; simp only [localFace,Pi.add_apply,map_add,smul_add]
lemma couple_move(s:Signed)(i j:PlaqAxes)(x:ℂ):localFace s (coupleW i j x)=coupleW (move s i) (move s j) ((levy s i*levy s j) • Pec.pays s x):=by rw [coupleW,local_plus, peg_follow,peg_follow,mul_comm (levy s j)]; rfl
lemma couple_swap (i j:PlaqAxes)(x:ℂ): coupleW i j x=coupleW j i x:= add_comm ..
lemma couple_neg (i j:PlaqAxes)(x:ℂ): coupleW i j (-x)= -(coupleW i j x):=by
 have t (i j:PlaqAxes): pegW i j (-x)= -(pegW i j x):= by funext u v; by_cases h:i=u ∧ j=v <;> simp [pegW,h]
 unfold coupleW; rw [t,t]; abel
lemma couple_mirror(a b c d:Axis)(v:Axis)(h:a<b)(u:c<d)(e:v=a∨v=b∨v=c∨v=d)(p:a≠c)(k:a≠d)(w:b≠c)(t:b≠d):
    let i:PlaqAxes:=⟨(a,b),h⟩; let j:PlaqAxes:=⟨(c,d),u⟩; localFace (Signed.mirror v) (coupleW i j Complex.I) = coupleW i j Complex.I:=by
 intro i j; let s:=Signed.mirror v; rw [couple_move]; have ht(i:PlaqAxes):move s i=i:=move_one i -- defeq
 rw [show move (Signed.mirror v) i= i from ht i, show move (Signed.mirror v) j = j from ht j]
 change coupleW _ _ ((levy s i*levy s j) • Pec.pays s _)=_; rw [show levy s i * levy s j= -1 from ?_]; · simp [Pec.pays,s,det_t]
 simp only [levy,StressFlux.sign,i,j, s,Signed.mirror,Equiv.refl_apply,h,u, Bool.decide_eq_true,if_true]; rcases e with rfl|rfl|rfl|rfl <;> simp [*,Ne.symm, (LT.lt.ne h), (LT.lt.ne u)] -- tune avoiding subst affecting i

private lemma inPlane_01: move inPlane lowLow=lowLow:= by decide
private lemma levy_inPlane_01: levy inPlane lowLow = -1 := by
 unfold levy StressFlux.sign; change (if false=true then (-1:ℝ) else 1)*(if false=true then (-1:ℝ) else 1)*(if (1:Axis) < 0 then 1 else -1)=_; norm_num [Axis] <;> decide

private lemma inPlane_02: move inPlane rimA=rimC:= by decide
private lemma levy_inPlane_02: levy inPlane rimA = 1 := by
 unfold levy StressFlux.sign; change (if false=true then (-1:ℝ) else 1)*(if false=true then (-1:ℝ) else 1)*(if (1:Axis) < 2 then 1 else -1)=_; norm_num [Axis] <;> decide

private lemma inPlane_03: move inPlane rimB=rimD:= by decide
private lemma levy_inPlane_03: levy inPlane rimB = 1 := by
 unfold levy StressFlux.sign; change (if false=true then (-1:ℝ) else 1)*(if false=true then (-1:ℝ) else 1)*(if (1:Axis) < 3 then 1 else -1)=_; norm_num [Axis] <;> decide

private lemma inPlane_12: move inPlane rimC=rimA:= by decide
private lemma levy_inPlane_12: levy inPlane rimC = 1 := by
 unfold levy StressFlux.sign; change (if false=true then (-1:ℝ) else 1)*(if false=true then (-1:ℝ) else 1)*(if (0:Axis) < 2 then 1 else -1)=_; norm_num [Axis] <;> decide

private lemma inPlane_13: move inPlane rimD=rimB:= by decide
private lemma levy_inPlane_13: levy inPlane rimD = 1 := by
 unfold levy StressFlux.sign; change (if false=true then (-1:ℝ) else 1)*(if false=true then (-1:ℝ) else 1)*(if (0:Axis) < 3 then 1 else -1)=_; norm_num [Axis] <;> decide

private lemma inPlane_23: move inPlane highHigh=highHigh:= by decide
private lemma levy_inPlane_23: levy inPlane highHigh = 1 := by
 unfold levy StressFlux.sign; change (if false=true then (-1:ℝ) else 1)*(if false=true then (-1:ℝ) else 1)*(if (2:Axis) < 3 then 1 else -1)=_; norm_num [Axis] <;> decide

private lemma outPlane_01: move outPlane lowLow=lowLow:= by decide
private lemma levy_outPlane_01: levy outPlane lowLow = 1 := by
 unfold levy StressFlux.sign; change (if false=true then (-1:ℝ) else 1)*(if false=true then (-1:ℝ) else 1)*(if (0:Axis) < 1 then 1 else -1)=_; norm_num [Axis] <;> decide

private lemma outPlane_02: move outPlane rimA=rimB:= by decide
private lemma levy_outPlane_02: levy outPlane rimA = 1 := by
 unfold levy StressFlux.sign; change (if false=true then (-1:ℝ) else 1)*(if false=true then (-1:ℝ) else 1)*(if (0:Axis) < 3 then 1 else -1)=_; norm_num [Axis] <;> decide

private lemma outPlane_03: move outPlane rimB=rimA:= by decide
private lemma levy_outPlane_03: levy outPlane rimB = 1 := by
 unfold levy StressFlux.sign; change (if false=true then (-1:ℝ) else 1)*(if false=true then (-1:ℝ) else 1)*(if (0:Axis) < 2 then 1 else -1)=_; norm_num [Axis] <;> decide

private lemma outPlane_12: move outPlane rimC=rimD:= by decide
private lemma levy_outPlane_12: levy outPlane rimC = 1 := by
 unfold levy StressFlux.sign; change (if false=true then (-1:ℝ) else 1)*(if false=true then (-1:ℝ) else 1)*(if (1:Axis) < 3 then 1 else -1)=_; norm_num [Axis] <;> decide

private lemma outPlane_13: move outPlane rimD=rimC:= by decide
private lemma levy_outPlane_13: levy outPlane rimD = 1 := by
 unfold levy StressFlux.sign; change (if false=true then (-1:ℝ) else 1)*(if false=true then (-1:ℝ) else 1)*(if (1:Axis) < 2 then 1 else -1)=_; norm_num [Axis] <;> decide

private lemma outPlane_23: move outPlane highHigh=highHigh:= by decide
private lemma levy_outPlane_23: levy outPlane highHigh = -1 := by
 unfold levy StressFlux.sign; change (if false=true then (-1:ℝ) else 1)*(if false=true then (-1:ℝ) else 1)*(if (3:Axis) < 2 then 1 else -1)=_; norm_num [Axis] <;> decide

private lemma exchangePlane_01: move exchangePlane lowLow=highHigh:= by decide
private lemma levy_exchangePlane_01: levy exchangePlane lowLow = 1 := by
 unfold levy StressFlux.sign; change (if false=true then (-1:ℝ) else 1)*(if false=true then (-1:ℝ) else 1)*(if (2:Axis) < 3 then 1 else -1)=_; norm_num [Axis] <;> decide

private lemma exchangePlane_02: move exchangePlane rimA=rimA:= by decide
private lemma levy_exchangePlane_02: levy exchangePlane rimA = -1 := by
 unfold levy StressFlux.sign; change (if false=true then (-1:ℝ) else 1)*(if false=true then (-1:ℝ) else 1)*(if (2:Axis) < 0 then 1 else -1)=_; norm_num [Axis] <;> decide

private lemma exchangePlane_03: move exchangePlane rimB=rimC:= by decide
private lemma levy_exchangePlane_03: levy exchangePlane rimB = -1 := by
 unfold levy StressFlux.sign; change (if false=true then (-1:ℝ) else 1)*(if false=true then (-1:ℝ) else 1)*(if (2:Axis) < 1 then 1 else -1)=_; norm_num [Axis] <;> decide

private lemma exchangePlane_12: move exchangePlane rimC=rimB:= by decide
private lemma levy_exchangePlane_12: levy exchangePlane rimC = -1 := by
 unfold levy StressFlux.sign; change (if false=true then (-1:ℝ) else 1)*(if false=true then (-1:ℝ) else 1)*(if (3:Axis) < 0 then 1 else -1)=_; norm_num [Axis] <;> decide

private lemma exchangePlane_13: move exchangePlane rimD=rimD:= by decide
private lemma levy_exchangePlane_13: levy exchangePlane rimD = -1 := by
 unfold levy StressFlux.sign; change (if false=true then (-1:ℝ) else 1)*(if false=true then (-1:ℝ) else 1)*(if (3:Axis) < 1 then 1 else -1)=_; norm_num [Axis] <;> decide

private lemma exchangePlane_23: move exchangePlane highHigh=lowLow:= by decide
private lemma levy_exchangePlane_23: levy exchangePlane highHigh = 1 := by
 unfold levy StressFlux.sign; change (if false=true then (-1:ℝ) else 1)*(if false=true then (-1:ℝ) else 1)*(if (0:Axis) < 1 then 1 else -1)=_; norm_num [Axis] <;> decide
lemma FF_even : PEven Ω₁∧PEven Ω₂:=by
 have q (s:Signed)(h:s∈ Loomed):localFace s Ω₁=Ω₁∧localFace s Ω₂=Ω₂:=by
    refine Submonoid.closure_induction (motive:=fun s _=> localFace s Ω₁=Ω₁∧localFace s Ω₂=Ω₂) ?_ ?_ ?_ h -- tune
    · rintro _ (⟨i,rfl⟩|d)
      · constructor
        · apply couple_mirror <;> revert i <;> decide
        rw [Ω₂,locale_sub];rw [show localFace (Signed.mirror i) (coupleW rimA rimD _)=(coupleW rimA rimD Complex.I) from by apply couple_mirror <;> revert i <;> decide,
                          show localFace (Signed.mirror i) (coupleW rimB rimC _)=(coupleW rimB rimC Complex.I) from by apply couple_mirror <;> revert i <;> decide]
      rw [Set.mem_insert_iff,Set.mem_insert_iff,Set.mem_singleton_iff] at d; rcases d with rfl|rfl|rfl
      · unfold Ω₁ Ω₂; simp_rw [locale_sub,couple_move]; simp only [inPlane_01, levy_inPlane_01, inPlane_02, levy_inPlane_02, inPlane_03, levy_inPlane_03, inPlane_12, levy_inPlane_12, inPlane_13, levy_inPlane_13, inPlane_23, levy_inPlane_23]; simp [Pec.pays,couple_swap,couple_neg] <;> abel
      · unfold Ω₁ Ω₂; simp_rw [locale_sub,couple_move]; simp only [outPlane_01, levy_outPlane_01, outPlane_02, levy_outPlane_02, outPlane_03, levy_outPlane_03, outPlane_12, levy_outPlane_12, outPlane_13, levy_outPlane_13, outPlane_23, levy_outPlane_23]; simp [Pec.pays,couple_swap,couple_neg] <;> abel
      · unfold Ω₁ Ω₂; simp_rw [locale_sub,couple_move]; simp only [exchangePlane_01, levy_exchangePlane_01, exchangePlane_02, levy_exchangePlane_02, exchangePlane_03, levy_exchangePlane_03, exchangePlane_12, levy_exchangePlane_12, exchangePlane_13, levy_exchangePlane_13, exchangePlane_23, levy_exchangePlane_23]; simp [Pec.pays,couple_swap,couple_neg] <;> abel
    · simp [local_one]
    intro x y _ _ a b; simp only [← local_m, a.1,b.1,b.2,a.2,true_and]
 exact ⟨fun s h=>(q s h).1,fun s h=>(q s h).2⟩
-- clover subspace
def cloverKey(x y:ℝ):Skate := x • Ω₁ + y • Ω₂

def ImagW (A:Skate):Prop:=∀ i j, star (A i j)= -(A i j)

lemma clover_imag(x y:ℝ): ImagW (cloverKey x y):=by
 intro i j; have he(a b:PlaqAxes):star (pegW a b Complex.I i j)= -(pegW a b Complex.I i j):=by unfold pegW; split_ifs<;>simp
 simp only [cloverKey,Ω₁,Ω₂,coupleW,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,star_sub,star_add,star_smul,he,star_trivial, neg_add,neg_sub_neg,smul_sub,smul_add,smul_neg]; abel -- simp loop

lemma sign_even (n:Side)(A:Skate):
    (∀ s∈twoPlanes n,costSkate s A=(pseudoCharacter n).sgn s • A) ↔ ImagW A∧ PEven A := by
 have H(i:Sweep n)(h:i.charge=false): costSkate i A=localFace i.s A:=by
    funext x y; obtain ⟨x,rfl⟩:=(move i.s).surjective x; obtain ⟨y,rfl⟩:=(move i.s).surjective y
    rw [cost_price,face_p,castT,Pec.complX,wageInv,show wageZ i=detX i.s from by unfold wageZ; rw [h,Bool.false_xor]] -- maybe `move` defeq
    rfl
 constructor
 · intro t; let i:Sweep n:=⟨1,0,true⟩
   constructor
   · intro x y; have h:=(cost_price i A x y); change _ at h; rw [t i (show i.s∈ Loomed from Loomed.one_mem),castT,wageInv,show wageZ i=true from by change true.xor (detX 1)= _; rw [det_i]; rfl,show PlaqAxes.transform i.s x= x from move_one x,show PlaqAxes.transform i.s y=y from move_one y,show spinScar i.s x=1 from levy_one x,show spinScar i.s y=1 from levy_one y,one_mul,one_smul] at h; change (-1:ℝ) • _= star (A x y) at h; simpa using h.symm
   intro s q; let i:Sweep n:=⟨s,0,false⟩; have hp:=t i q; rw [H i rfl] at hp; exact hp.trans (one_smul _ _)
 rintro ⟨f,h⟩ i b; have ht:=h i.s b
 cases v:i.charge
 · rw [H i v,ht]; change _=hush i.charge (1:ℝ) • A; rw [v,hush_false,one_smul]
 funext x y; obtain ⟨x,rfl⟩:=(PlaqAxes.transform i.s).surjective x; obtain ⟨y,rfl⟩:=(PlaqAxes.transform i.s).surjective y
 change costSkate i A (move i.s x) (move i.s y) = hush i.charge (1:ℝ) • (A _ _)
 rw [v,hush_true,neg_one_smul]; have hp:=face_p i.s A x y; rw [ht] at hp
 -- adjust defeq move.
 rw [cost_price,hp,castT,Pec.complX,wageInv]; change _ • cSignX _ _ = -((spinScar i.s x*spinScar i.s y) • cSignX _ _); unfold wageZ; rw [v]; cases detX i.s<;>simp [cSignX,f x y] -- tune

lemma clover_verc (x y:ℝ) : cloverKey x y∈mind_A:= (mind_A.restrictScalars ℝ).add_mem ((mind_A.restrictScalars ℝ).smul_mem x (couple_Verc _ _ _)) ((mind_A.restrictScalars ℝ).smul_mem y (mind_A.sub_mem (couple_Verc _ _ _) (couple_Verc _ _ _)))
lemma clover_in (x y:ℝ) (n:Side) (s:Sweep n)(h:s∈twoPlanes n):costSkate s (cloverKey x y)=(pseudoCharacter n).sgn s • cloverKey x y:=
 (sign_even ..).2 ⟨clover_imag x y,fun p v=>by unfold cloverKey; rw [local_plus,locale_smul,locale_smul,FF_even.1 p v,FF_even.2 p v]⟩ s h

private lemma imaginary_form(z:ℂ)(p:star z= -z):z=z.im • Complex.I:=by
 apply Complex.ext
 · have ht:= congrArg Complex.re p; simp at ht; simp; linarith
 simp

-- off complementary: only need a common axis. Then both parity factors -1.
private lemma no_overlap(i:Axis)(a b:PlaqAxes)(A:Skate)(p:ImagW A)(t:PEven A)(u:i=a.val.1∨i=a.val.2)(v:i=b.val.1∨i=b.val.2) : A a b=0:=by
 let s:=Signed.mirror i
 have h(a:PlaqAxes)(u:i=a.val.1∨i=a.val.2) : levy s a= -1:=by
    simp only [levy,StressFlux.sign]; rcases u with e|e <;> simp [e,s,Signed.mirror,a.property,a.property.ne,a.property.ne.symm]
 have ht:= face_p s A a b; rw [t _ (mirror_l _), h a u,h b v,show move s a=a from move_one a, show move s b=b from move_one b] at ht
 apply neg_forces _; unfold s at ht; simpa [Pec.complX,det_t,cSignX,p a b] using ht

lemma clover_sector (n:Side)(A:Skate):
    (A∈mind_A ∧∀ s∈twoPlanes n,costSkate s A=(pseudoCharacter n).sgn s • A) ↔ ∃ x y:ℝ, A=cloverKey x y:=by
 constructor
 · rintro ⟨p,t⟩; obtain ⟨f,q⟩:=(sign_even ..).1 t
   have P:Verc A:=p
   let x:= (A lowLow highHigh).im; let y:=(A rimB rimC).im
   have Z:Verc (cloverKey x y):=clover_verc x y; have W := clover_imag x y
   obtain ⟨_,Q⟩ := (sign_even n _).1 (clover_in x y n)
   have v₁:A lowLow highHigh=cloverKey x y lowLow highHigh:=by
      refine Eq.trans (imaginary_form _ (f ..)) ?_; unfold cloverKey Ω₁ Ω₂ coupleW pegW; simp only [Pi.add_apply,Pi.smul_apply, Pi.sub_apply]; simp +decide; rfl
   have v₂:A rimB rimC=cloverKey x y rimB rimC:=by
      refine Eq.trans (imaginary_form _ (f ..)) ?_; unfold cloverKey Ω₁ Ω₂ coupleW pegW; simp only [Pi.add_apply,Pi.smul_apply, Pi.sub_apply]; simp +decide; rfl
   have N(A:Skate)(p:Verc A)(f:ImagW A)(t:PEven A) : A rimA rimD= -(A rimB rimC):=by
      have ht:=face_p outPlane A rimB rimC; rw [t _ out_l,outPlane_03,outPlane_12,levy_outPlane_03,levy_outPlane_12, one_mul,one_smul,Pec.complX] at ht; exact ht.trans (by rw [det_outp]; exact (f ..))
   refine ⟨x,y,?_⟩; have h(a b:PlaqAxes)(i:Axis)(u:i=a.val.1∨i=a.val.2)(v:i=b.val.1∨i=b.val.2): A a b=cloverKey x y a b:= (no_overlap i a b A f q u v).trans (no_overlap i a b _ W Q u v).symm -- orientation
   have v₃: A rimA rimD=cloverKey x y rimA rimD:=(N A P f q).trans ((congrArg Neg.neg v₂).trans (N _ Z W Q).symm)
   funext a b
   rcases rimCases a with ha|ha|ha|ha|ha|ha <;> rcases rimCases b with e|e|e|e|e|e <;> subst a <;> subst b
   · exact h lowLow lowLow 0 (by decide) (by decide)
   · exact h lowLow rimA 0 (by decide) (by decide)
   · exact h lowLow rimB 0 (by decide) (by decide)
   · exact h lowLow rimC 1 (by decide) (by decide)
   · exact h lowLow rimD 1 (by decide) (by decide)
   · exact v₁
   · exact h rimA lowLow 0 (by decide) (by decide)
   · exact h rimA rimA 0 (by decide) (by decide)
   · exact h rimA rimB 0 (by decide) (by decide)
   · exact h rimA rimC 2 (by decide) (by decide)
   · exact v₃
   · exact h rimA highHigh 2 (by decide) (by decide)
   · exact h rimB lowLow 0 (by decide) (by decide)
   · exact h rimB rimA 0 (by decide) (by decide)
   · exact h rimB rimB 0 (by decide) (by decide)
   · exact v₂
   · exact h rimB rimD 3 (by decide) (by decide)
   · exact h rimB highHigh 3 (by decide) (by decide)
   · exact h rimC lowLow 1 (by decide) (by decide)
   · exact h rimC rimA 2 (by decide) (by decide)
   · rw [P rimC rimB, Z rimC rimB]; exact v₂
   · exact h rimC rimC 1 (by decide) (by decide)
   · exact h rimC rimD 1 (by decide) (by decide)
   · exact h rimC highHigh 2 (by decide) (by decide)
   · exact h rimD lowLow 1 (by decide) (by decide)
   · rw [P rimD rimA, Z rimD rimA]; exact v₃
   · exact h rimD rimB 3 (by decide) (by decide)
   · exact h rimD rimC 1 (by decide) (by decide)
   · exact h rimD rimD 1 (by decide) (by decide)
   · exact h rimD highHigh 3 (by decide) (by decide)
   · rw [P highHigh lowLow, Z highHigh lowLow]; exact v₁
   · exact h highHigh rimA 2 (by decide) (by decide)
   · exact h highHigh rimB 3 (by decide) (by decide)
   · exact h highHigh rimC 2 (by decide) (by decide)
   · exact h highHigh rimD 3 (by decide) (by decide)
   · exact h highHigh highHigh 2 (by decide) (by decide)
 rintro ⟨x,y,rfl⟩; exact ⟨clover_verc x y,clover_in x y n⟩
lemma clover_at_first(x y:ℝ) : cloverKey x y lowLow highHigh=x • Complex.I:=by unfold cloverKey Ω₁ Ω₂ coupleW pegW; simp only [Pi.add_apply,Pi.smul_apply, Pi.sub_apply]; simp +decide
lemma clover_at_second(x y:ℝ) : cloverKey x y rimB rimC=y • Complex.I:=by unfold cloverKey Ω₁ Ω₂ coupleW pegW; simp only [Pi.add_apply,Pi.smul_apply, Pi.sub_apply]; simp +decide
end YM.CF.QuadClock
