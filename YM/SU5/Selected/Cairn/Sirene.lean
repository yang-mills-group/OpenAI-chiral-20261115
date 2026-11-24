import YM.SU5.Selected.Cairn.Rhys
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Pannier.Chancel.Attic.Cairn
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest Airy Rail Lantern Lantern.Bulb Attic Cuve
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 20000
local notation "I"=>Complex.I
open Mint Rubric Stencil
open Mezz
private lemma tape_I {n q:Type*}[Fintype n][LinearOrder n][Fintype q][DecidableEq q](X:WRect n q)(i:Fintype.card q=10): tape true (Complex.I • X)= -tape true X:=by
 have he: tape true (Complex.I • X)= tone true (Complex.I ^ Fintype.card q) • tape true X :=by
    calc _ = tape true (X*(Complex.I • (1:Op q))):= by rw [Matrix.mul_smul,Matrix.mul_one]
         _ = tone true (Complex.I ^ Fintype.card q) • tape true X:=by rw [wave_det,Matrix.det_smul,Matrix.det_one,mul_one]
 apply he.trans; rw [i,show (10:ℕ)=2*5 from rfl,pow_mul,Complex.I_sq]; change star ((-1:ℂ)^ (5:ℕ)) • _=_; norm_num
private lemma tape_scaled {n q:Type}[Fintype n][LinearOrder n][Fintype q][DecidableEq q](X Z:WRect n q)(k:pulseNode): rune k (Complex.I • X) (Complex.I • Z)= Complex.I • rune k X Z:=by unfold rune; rw [smul_add,smul_comm]
namespace Giant
open Afterglow Tower Tower.SlabMark Tapestry
attribute [local instance] opCStarAlgebra
variable (A:Giant) {N:Side}(Z:A.Notes→basisRule) {T:Type}[Fintype T][DecidableEq T](P:Society T)(b y:Bool)(i:A.Block)(C:ℝ)
local notation "J" b:max t:max=> A.Hours (N:=N) Z P true b C i t
local notation "p"=>A.TourA.speed
local notation "V"=>shuffleW p N
lemma flash (U:Pane N) : A.fleur Z P true true i C U= -(twist (quantU V) (A.fleur Z P true false i C (shuffleG p U))):=by
 unfold fleur; simp_rw [loreP true _ _ P.club_card,map_sum,twist_scalar]; rw [←sum_neg_distrib]; apply sum_congr rfl; intro j _; rw [hourE A Z P i C true,hourE A Z P i C false,tape_scaled,tape_I _ P.club_card,tape_cov,smul_neg]; unfold rune; rw [Matrix.mul_add,Matrix.mul_smul]
variable {M:Tulip.Male}{γ δ:ℝ}(c:Pride A Z C δ γ M N)(z:A.tokenS<N.val)
include c z
lemma toneness: A.tonne (N:=N) Z P true true i C= -reflMark 3 p (reflMark 3 0 (A.tonne Z P true false i C)):=by
 funext x; rw [Pi.neg_apply, Mezz.hover _ _ x (A.tonne_guard Z P true false i C c z)]; exact flash .. -- args
-- family on Room extends charge EXACT.
omit c z
variable (K:Calibration)
variable {m:Side} (c': Pride A Z C δ γ M (K.c m))
local notation "κ" => K.c m
local notation "τ"=> P.qu.kin
local notation "Λ"=> A.patio b
local notation "σ₀"=> park (K.c m)
local notation "Σ"=> A.Zumba
local notation "Υ" a:max=> K.b -- remove
local notation "Γ" S:max=> Rubric.Reach K P.qu.kin A.Zumba A.ascX A.ascY S m
local notation "𝒩"=> modesIn
include c'
lemma lamp_age (U:Pane κ): A.fleur Z P b y i C U∈ (Γ (A.patio b)) (lv_one b) (lv_one (!b)) (priorityR b):=by
 have ht(F H: WRect (Single (κ)) P.Club)(b:Bool)(r s n:ℕ)(k:∀ t:P.Club, creed b (col F t)∈ (Γ (A.patio b)) r s n)(q:∀ t:P.Club, creed b (col H t)∈ (Γ (A.patio b)) r s 0): countOne F H b∈ (Γ (A.patio b)) (10*r) (10*s) n:= by have ht:= Reach.rake_reserves _ _ k q Finset.univ.toList 1; rw [rung_len P.club_card, one_mul] at ht; exact ht
 let f(b t:Bool):WRect (Single (κ)) P.Club:= A.Hours Z P b y C i t U; cases b
 · have hd: Disjoint A.Zumba A.ascY:= Disjoint.mono (filter_subset ..) (subset_refl _) A.are_d.symm
   have hv(t x): creed false (col (f false t) x)∈ (Γ (A.patio false)) 0 1 0:= by
        let T:= A.filmR Z P C U; apply Reach.create_zone _ _ A.ascY _ (subset_refl _) (subset_refl _) hd;
        · exact (containedT ..).mp ((A.labelR Z P C U).times (mask (fun j:P.Club=>(t,i,j)))) x
        · exact (col_lim ..).mpr (A.desc_s P i t (A.fluf Z P U c')) x
        exact (containedT ..).mp ((A.floraY Z P C U c'.crop).times _) x
   exact ht _ _ _ 0 1 0 (hv true) (hv false)
 have hv(t x): creed true (col (f true t) x)∈ (Γ (A.patio true)) 1 0 (priorityR t):= by
    let T:= A.filmL P y C U; refine Reach.remove_zone ((containedT ..).mp ((A.labelL P y C U).times (mask (fun j:P.Club=>(t,i,j)))) x) ?_ (A.Knot t) ((containedT ..).mp (A.floral ..) x) (A.knot_x t) (A.knot_x t) (fun i e=>?_)
    · unfold withinM; rw [dim_cut]; exact (col_lim ..).mpr (A.desc_s P i t (A.flora_pitch P y C U)) x -- col_lim orientation mpr
    simp only [knot_root A t e]
 unfold fleur; exact ht _ _ true 1 0 1 (hv true) (hv false)
end Giant
end YM.CF.Pannier.Chancel.Attic.Cairn
open YM.CF.Pannier.Chancel.Attic.Cairn.Giant
#print axioms toneness
#print axioms lamp_age
