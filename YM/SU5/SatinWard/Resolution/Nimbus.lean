import YM.SU5.SatinWard.Resolution.Highway
import SatinThinCarry
import YM.SU5.SatinWard.Resolution.Canvas
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 85000
noncomputable section
set_option linter.unusedSectionVars false
set_option quotPrecheck false
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
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
open Ione Beau Haro Cascade Fief
open scoped Mew
open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Eire Girt
open VolumeRate
open BScale Vow.TreasuryFog Sour Roots Exa Vow Rive Mew Stax Swell Porticus QuadClock Ione.Clock Moto Neon Taxi Lor
open Oise Buffered
open Pitching Focus QuadClock.ShapeLab
open Oise Buffered
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ)) (Γ:ℝ)(Pay kc:ℝ)(Tξ:Hove.Grant P.K.j 2)(nmc m:ℕ) (Z V K W:ℝ→ℝ)
variable {η ι:Type}[Fintype ι][DecidableEq ι][Fintype η](F:ResolutionFrame ι)(C H A:ℝ)
open Pail.Dew Swell.Porticus QuadClock.ShapeLab.ResolutionFrame
open Lampshade SignSlot Waxy Tap
variable {a b c d U ε f r ψ:ℝ}{s i k:ℕ}
local notation "Λ" => P.Ctor (Y.ir i) s
local notation "θ"=>lapQ Y s
local notation "ωs"=> hat P.R.L P.x s
open Hove Yoke Buffered Afterglow Journey ShapeLab.ResolutionFrame
namespace Tabletop

open ResolutionFrame Vow.TreasuryFog Swell
variable {I J:Type}[Fintype I][LinearOrder I][DecidableEq J](σ:I→J)(C₀:I→ I→ℂ)
lemma totalSnow {X:Type*}[MeasurableSpace X] (μ:Measure X)(l:List I)(f:List I→X→ℂ)(p:∀ z:List I,z.map σ=l.map σ→Integrable (f z) μ): Integrable (fun x=>Roots.snow σ C₀ (fun t=>f t x) l) μ∧ (∫ x,Roots.snow σ C₀ (fun t=>f t x) l∂μ)= Roots.snow σ C₀ (fun t=> ∫ x,f t x∂μ) l:=by
 induction l generalizing f with
 | nil=> exact ⟨p _ rfl,rfl⟩
 | cons i l ih=>
    have ht(j:I)(g:j∈pipe_ζ σ i):=ih (fun t=> f (j::t)) (fun z v=> p _ (by rw [List.map_cons,List.map_cons, (mem_filter.mp g).2,v]))
    have hu(j:I)(w:j∈pipe_ζ σ i): Integrable (fun x=> C₀ j i • (Roots.snow σ C₀ (fun t=> f (j::t) x) l)) μ:= (ht j w).1.smul (C₀ j i) -- scalar ABI
    simp only [Roots.snow]; refine ⟨ integrable_finsetSum _ hu, (integral_finsetSum _ hu).trans (sum_congr rfl fun j g=> ?_)⟩
    rw [integral_smul,(ht j g).2]
-- mark layout.M. price ``all``. Then later strengthen for Beyond. Snow lemma allows univ throughout limits.
open ResolutionFrame Rue
lemma caféCost {κ:Type*}(A:Finset κ)(V:κ→ Mark (P.Ctor (Y.ir i) s))(t:∀ i∈A,AtSupport false Finset.univ (V i))(p:Version (city (P.Ctor (Y.ir i) s)) (morning Y i k s)) : AtSupport false Finset.univ (∑ i∈A,V i) ∧ mark_cost Y i k s (∑ i∈A,V i)=∑ j∈A,mark_cost Y i k s (V j) := by
 induction A using Finset.induction_on with
 | empty=> simp_rw [sum_empty]; refine ⟨AtSupport.zeroM,?_⟩; -- can avoid simpl
           have he:=palm_scale (f:=s) Y i (α:=morning Y i k s) (0:Mark (P.Ctor (Y.ir i) s)) 0; rw [smul_zero,zero_smul] at he; exact he
 | insert j S h ih=> simp only [sum_insert h]; obtain ⟨hV,hu⟩:= ih (fun i p'=>t _ (mem_insert_of_mem p')); refine ⟨(t j (mem_insert_self ..)).addM hV,?_⟩; unfold mark_cost; rw [palm_plus Y i _ (t j (mem_insert_self ..)).env hV.env p]; exact congrArg (_ + ·) hu
abbrev markBy {N:Side}(f:I→ Mark N) (i:I):Mark N:= ∑ j∈pipe_ζ σ i,C₀ j i • f j
lemma masks_markBy {N':Side}(S:I→ Support (More N'))(V:I→ Mark N')(p:∀ i,AtSupport false (S i) (V i))(h:∀ (i j:I), σ j=σ i→ S j=S i)(i:I): AtSupport false (S i) (markBy σ C₀ V i):=by
 have ht(t:Finset I)(h':t⊆ pipe_ζ σ i): AtSupport false (S i) (∑ j∈t,C₀ j i • V j):=by
    induction t using Finset.induction_on with
    | empty=> rw [sum_empty]; exact AtSupport.zeroM
    | insert j t v ih=> rw [sum_insert v]; obtain ⟨k,q⟩:= insert_subset_iff.mp h'; exact ((h _ _ (mem_filter.mp k).2) ▸ (p j).smulM _).addM (ih q)
 exact ht _ (Finset.Subset.refl _)
lemma markBy_cost (p:Version (city (P.Ctor (Y.ir i) s)) (morning Y i k s))(V:I→ Mark (P.Ctor (Y.ir i) s))(kG:∀ i,AtSupport false Finset.univ (V i))(F:Mark (P.Ctor (Y.ir i) s))(g:AtSupport false Finset.univ F)(l:List I): Roots.snow σ C₀ (fun l=> mark_cost Y i k s (F*(l.map V).prod)) l= mark_cost Y i k s (F*(l.map (markBy σ C₀ V)).prod):=by
 induction l generalizing F with
 | nil=>rfl
 | cons j l ih=>
    let W':= (l.map (markBy σ C₀ V)).prod; let A:=mark_cost Y i k s; have hz:AtSupport false univ W':=receipt_word (masks_markBy σ C₀ (fun _=>Finset.univ) V kG (fun _ _ _=>rfl)) l (fun _ _=> Finset.Subset.refl _)
    change Roots.snow σ C₀ _ _= A (F*(markBy σ C₀ V j*W')); unfold Roots.snow; -- only once?
    have ht(i':I):Roots.snow σ C₀ (fun t:List I=> A (F*((i'::t).map V).prod)) l=A ((F*V i')*W'):=by refine (rer _ _ _ (G:=fun t:List I=> A (F* ((i'::t).map V).prod)) (W:=fun t=> A ((F*V i')*(t.map V).prod)) ?_).trans (ih _ (g.mulM (kG i'))); intro t _; simp only [List.map_cons,List.prod_cons,mul_assoc]
    let T (x:I):Mark (P.Ctor (Y.ir i) s):=(F*V x)*W'; let H(x:I):Mark (P.Ctor (Y.ir i) s):= C₀ x j • T x; have ht'(i:I):AtSupport false univ (H i):=((g.mulM (kG i)).mulM hz).smulM _
    have he:F*(markBy σ C₀ V j*W')= ∑ i∈pipe_ζ σ j,H i:= by
       unfold markBy; rw [Finset.sum_mul, Finset.mul_sum]; exact sum_congr rfl fun t _=> (by unfold H T; rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,mul_assoc])
    rw [he]; refine (Eq.trans (b:=∑ i'∈pipe_ζ σ j,A (H i')) ?_ (caféCost Y _ H (fun i _=>ht' i) p).2.symm); refine sum_congr rfl fun t _=> ?_; change C₀ t j • Roots.snow σ C₀ _ _= A (H t); rw [ht t]; exact (palm_scale Y i _ (α:=morning Y i k s) _).symm
lemma snows_cost (p:Version (city (P.Ctor (Y.ir i) s)) (morning Y i k s))(V:I→ Mark (P.Ctor (Y.ir i) s))(kG:∀ i,AtSupport false Finset.univ (V i))(l:List I): Roots.snow σ C₀ (fun t=> mark_cost Y i k s (t.map V).prod) l= mark_cost Y i k s (l.map (markBy σ C₀ V)).prod:=by simpa only [one_mul] using markBy_cost Y σ C₀ p V kG 1 (AtSupport.oneM _) l
#print axioms snows_cost
end Tabletop
end YM.CF.Py.Rate.LocalLimit.Preparation
