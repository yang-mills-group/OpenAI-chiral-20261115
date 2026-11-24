import YM.SU5.SatinWard.Resolution.ColourFrame
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
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
variable {N n B₀:Side}
open Tap Waxy Ione.Clock StressFlux SU
namespace ShapeLab
open Module
local notation "EndC"=> Op SU.Slot
variable {ι:Type}[Fintype ι][DecidableEq ι]

-- End and turns. Preliminary rank receipts. Don't replace operator norm on preparation.
namespace SoulField
open Mezzo
variable {j:Axis}{U V:UNI SU.Slot}(h:Registrar U)(v:Registrar V)
local notation "Jι"=> Wage3

namespace Treaty
local notation "M"=> TuneM
local notation "I"=> (Fin 3)
local notation "Θ" z:max=> (Reg z).val
local notation "C"=> Complex.I
variable (q: UNI (Fin 3))(b:Bool)(i j: Fin 3)
variable (z:Soul)(e:i≠j)
lemma concertTurn : ribbon b (rotor (registrar_vote (q,q)) z) = twist q (ribbon b z):=by
 let U:=attuned q; let Z:= rotor (registrar_vote (q,q)) z; have hp: (sonnet (ribbon true Z) (ribbon false Z))= sonnet (twist q (ribbon true z)) (twist q (ribbon false z)):=by rw [score_bracket]; rw [show (Reg Z).val= _ from rotor_pay .., ←score_bracket,rotate_vote];
 obtain ⟨h,u⟩:=coeffInj hp; cases b; exact u; exact h
abbrev earL(i:I): M:= Matrix.single i i 1
abbrev earM(i j:I): M:=Matrix.single i j 1+ Matrix.single j i 1
abbrev peakMark (i j:I):M:= Matrix.single i j Complex.I+ Matrix.single j i (-Complex.I)
lemma sharedStar {α:Type}[Fintype α][DecidableEq α](i j:α)(z:ℂ):star (Matrix.single i j z)= Matrix.single j i (star z):=by ext x y; by_cases h:i=y <;> by_cases w:j=x<;> simp [h,w]
lemma sharedCc {α:Type}[Fintype α][DecidableEq α](i j:α)(z:ℂ):cc (Matrix.single i j z)= Matrix.single i j (star z):=by ext x y; by_cases h:i=x <;> by_cases w:j=y<;> simp [h,w]
lemma mercy : star (earL i)=earL i:=by rw [earL, sharedStar i i,star_one]
lemma married : star (earM i j)=earM i j:=by unfold earM; rw [star_add, sharedStar,sharedStar,star_one,add_comm]
lemma coolF : cc (earL i)=earL i:=by rw [earL,sharedCc,star_one]
lemma coolPair: cc (earM i j)=earM i j:=by unfold earM; rw [cc_add,sharedCc,sharedCc,star_one]
lemma partnerSelf:star (peakMark i j)=peakMark i j:=by unfold peakMark; rw [star_add,sharedStar,sharedStar,add_comm]; simp
noncomputable abbrev pivotL (b:Bool)(i:Fin 3): Soul:= patchH b (earL i) (mercy i)
noncomputable abbrev buyerV (b:Bool)(i j:Fin 3):Soul:=patchH b (earM i j) (married ..)
noncomputable abbrev sellerV(b:Bool)(i j:Fin 3):Soul:=patchH b (peakMark i j) (partnerSelf ..)
noncomputable def examples : Set Soul:={x| ∃ (U:UNI SU.Slot) (h:Concert U) (z:Soul), cc (Reg z).val=(Reg z).val ∧ x=rotor h.gate z-z}
noncomputable def rotationHull: Submodule ℝ Soul:= Submodule.span ℝ examples
lemma rotational {a:Soul} (w:cc (Θ a)=Θ a){U:UNI SU.Slot}(h:Concert U): rotor h.gate a-a∈ rotationHull:= Submodule.subset_span (show rotor h.gate a-a∈ examples from ⟨U,h,a,w,rfl⟩)
lemma contained : rotationHull≤depth:=by
 refine Submodule.span_le.mpr (fun x hx=>?_); obtain ⟨U,e,q,s,rfl⟩:=hx; exact (depth_iff _).2 (fun i=>by rw [map_sub,genConcert,sub_self])
private lemma spinGuide (q:UNI (Fin 3))(a z:Soul){b:Bool}(p:ribbon (!b) a=0)(e:ribbon (!b) z=0) (t:twist q (ribbon b a)=ribbon b z): rotor (registrar_vote (q,q)) a=z:=by
 apply duplicate b; rw [concertTurn,t]; rw [concertTurn,p,e,map_zero]
local notation "R" b:max=>ribbon b
include e in
lemma meander :∃ (T:UNI (Fin 3)), Concert (attuned T)∧ twist T (earL i)=earL j:=by
 obtain ⟨c,h,t⟩:=(show ∀ a b:I,∃ c:I,c≠a ∧ c≠b from by decide) i j; let f:=(Equiv.swap j c).trans (Equiv.swap i j); let a:= f.trans f
 let Z:= progressV i j c; refine ⟨Z,concert_a ..,?_⟩; have ht:Z=hairU a:=Subtype.ext (progress_view ..); rw [ht]; change twist (hairU _) _=_; unfold earL; rw [←Matrix.diagonal_single, ← Matrix.diagonal_single, twirlMove]; congr 1; funext k; have he:a j=i:=by unfold a f; simp [Equiv.swap_apply_of_ne_of_ne h t]
 by_cases u:k=j; · simp [u,he]
 have hv:a k≠i:=fun p=>u (a.injective (p.trans he.symm)); simp [hv,u]
lemma walls : pivotL b i-pivotL b j ∈ rotationHull:=by
 by_cases h:i=j; subst j; simp
 obtain ⟨U,v,p⟩:= meander j i (Ne.symm h); let u:= pivotL b j; rw [show pivotL b i=rotor v.gate u from ?_]; exact rotational (valid_arm b (mercy j) (coolF ..)) v
 exact (spinGuide U u _ (b:=b) (patch_away ..) (patch_away ..) (by unfold u pivotL; rw [patch_here,patch_here]; exact p)).symm
private lemma heardD {α:Type}[Fintype α][DecidableEq α](q:UNI α)(v:α→ℂ)(u:q.val=Matrix.diagonal v) (i j:α)(z:ℂ): twist q (Matrix.single i j z)= Matrix.single i j (v i*z*star (v j)):=by
 rw [twist_formula,u,Matrix.star_eq_conjTranspose,Matrix.diagonal_conjTranspose]; ext a b; simp only [Matrix.mul_diagonal,Matrix.diagonal_mul]; by_cases h:i=a<;>by_cases t:j=b <;>simp [h,t]
include e
lemma croquet : ∃ (T:UNI (Fin 3)), Concert (attuned T) ∧ twist T (earM i j) = -earM i j:=by
 obtain ⟨c,h,t⟩:=(show ∀ a b:I,∃ c:I,c≠a ∧ c≠b from by decide) i j; let Q:= pealU i*pealU c; let d:= blastSign i*blastSign c; have v:Q.val=Matrix.diagonal d:= Matrix.diagonal_mul_diagonal _ _; refine ⟨Q,partner i c,?_⟩
 have he:d i=-1:=by simp [d,blastSign,Mezzo.peal,h]
 have ht:d j=1:=by simp [d,blastSign,Mezzo.peal,t,e]
 unfold earM; rw [map_add,heardD _ _ v,heardD _ _ v,he,ht]; simp [Matrix.single_neg,add_comm]
lemma at_toll : buyerV b i j∈ rotationHull:=by
 obtain ⟨U,k,p⟩:= croquet i j e; let z:= buyerV b i j
 have he:rotor k.gate z = -z:=by refine spinGuide U z (-z) (b:=b) (?_) (?_) (?_); exact patch_away ..; rw [map_neg,show ribbon (!b) z=0 from patch_away .., neg_zero]; unfold z buyerV; rw [map_neg,patch_here,p]
 have hv:= rotational (valid_arm b (married i j) (coolPair ..)) k; change rotor _ z-z∈ _ at hv; change z∈_; rw [he] at hv; convert Submodule.smul_mem rotationHull (-1/2:ℝ) hv using 1; module
omit e
noncomputable abbrev crescent (i:Fin 3)(x:Fin 3):ℂ:= if x=i then Complex.I else 1
noncomputable def pearlT(i:I): UNI I:=by
 let U:=Matrix.diagonal (crescent i); refine ⟨U,?_⟩; apply Matrix.mem_unitaryGroup_iff.mpr; change U*star U=1; unfold U; rw [Matrix.star_eq_conjTranspose,Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]; ext x y; by_cases v:x=y; subst y; rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]; by_cases h:x=i <;> simp [h,crescent]; simp [v]
include e
lemma finalView : ∃ (T:UNI (Fin 3)), Concert (attuned T)∧ twist T (earM i j)= peakMark i j:=by
 obtain ⟨c,h,t⟩:=(show ∀ a b:I,∃ c:I,c≠a ∧ c≠b from by decide) i j; let V:=shiftU i c; let U:=pearlT c; let T:= V*U*V⁻¹*U⁻¹; refine ⟨T,concert_a ..,?_⟩
 let d(z:I):=crescent c ((Equiv.swap i c) z)*star (crescent c z); have hp:T.val=Matrix.diagonal d:=by
    change V.val*U.val*star V.val*star U.val=_; rw [←twist_formula V U.val]; change twist (hairU _) (pearlT c).val*star (pearlT c).val=_; rw [show (pearlT c).val=Matrix.diagonal (crescent c) from rfl,twirlMove,Matrix.star_eq_conjTranspose,Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]; rfl
 have ht: d i=C:=by simp [d,crescent,h.symm]
 have h': d j=1:=by rw [show d j=crescent c j*star (crescent c j) from ?_]; simp [crescent,t.symm]; unfold d; rw [Equiv.swap_apply_of_ne_of_ne e.symm t.symm]
 unfold earM peakMark; rw [map_add,heardD _ _ hp,heardD _ _ hp,ht,h']; simp
lemma underK : sellerV b i j∈ rotationHull:=by
 obtain ⟨U,k,p⟩:=finalView i j e; let z:= buyerV b i j
 have he:rotor k.gate z=sellerV b i j:=by refine spinGuide U z _ (b:=b) (?_) (?_) (?_); exact patch_away ..; exact patch_away ..; unfold z buyerV sellerV; rw [patch_here,patch_here,p]
 have hv:= rotational (valid_arm b (married i j) (coolPair i j)) k; change rotor _ z-z∈ _ at hv; rw [he] at hv; exact sub_add_cancel (sellerV b i j) z ▸ Submodule.add_mem rotationHull hv (at_toll b i j e)
#print axioms underK
end Treaty
end SoulField
end ShapeLab
end YM.CF.QuadClock

