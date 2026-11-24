import YM.SU5.Reconstruction.Hygrometry.Landing
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 30000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Hygrometry
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Tulip Phase
open Laurent Next.Free Bloch Fir Ember Jill Kea Sods Flare Emu Onyx Dial
open Filter Topology
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open YM.CF.Buffered YM.CF.Window
open YM.Stationary (Gaia)
open Mir Reflect Buffered.Lifted Buffered.Afterglow.Tower.Tilted
open PriceCliff RP
variable {N m B:Side} {α β:Type*} [Fintype β]
-- finite sums scalar charges true Wick roots on these probes.
def wheat {α:Type*}: List α→ Bool
 | []=>false
 | _::xs=> true.xor (wheat xs)
lemma wheat_grade (w:List α): wheat w= decide (w.length%2=1):=by induction w with
 | nil=>rfl
 | cons i l ih=> rw [wheat,ih,List.length_cons]; have ht:= Nat.mod_two_eq_zero_or_one l.length; cases ht with
    | inl he=> rw [Nat.add_mod,he]; rfl
    | inr he=> rw [Nat.add_mod,he]; rfl

noncomputable def utter (X:α→ Cover)(Z:α→Personality)(N:Side)(r:ℝ)(F:β→List α)(u:β→ℂ):=∑ i:β, u i • literal X Z N r (F i)
abbrev Packed (M:ActMark)(Z:α→Personality):α ⊕ α→Personality:= Sum.elim (M.role ∘ Z) Z
noncomputable def couple (C D:List α) : List (α ⊕ α):= C.map Sum.inl ++ D.map Sum.inr
variable (M:ActMark) (K:Gaia→Gaia)(X:α→ Gaia)(Y:α→ Cover)(Z:α→Personality) (R:ℝ) (F:β→ List α)(u:β→ℂ)
local notation "Xz" => Sum.elim (K ∘ X) X
local notation "tG" => posted M Y
noncomputable def harvestCost (b:Bool):ℂ:=∑ i:β,∑ j:β,(Reflect.chord b*star (u i)*u j*ActMark.royalties Z (F i))*quantum (Sum.elim (K ∘ X) X) (Packed M Z) (couple (F i) (F j))
noncomputable def poseX (M:ActMark)(b:Bool)(A:FC (Single N)):=Reflect.chord b • (Fock.theta (M.turnout N) A*A)
abbrev priceWeight (b:Bool)(i j:β):ℂ:= Reflect.chord b * star (u i)*u j*ActMark.royalties Z (F i)
private lemma tells (P Q:List α) : Fock.theta (M.turnout N) (literal Y Z N R P)*literal Y Z N R Q= ActMark.royalties Z P • literal (posted M Y) (Packed M Z) N R (couple P Q):= by
 rw [M.shifts,Matrix.smul_mul]; apply congrArg (ActMark.royalties Z P • ·); unfold literal couple rollC; rw [List.map_append, List.prod_append,List.map_map,List.map_map]; rfl
local notation "A" => utter Y Z N R F u
lemma runCost(b:Bool): poseX M b A= ∑ i:β,∑ j:β, priceWeight Z F u b i j • literal (posted M Y) (Packed M Z) N R (couple (F i) (F j)):=by
 unfold poseX utter; rw [theta_sum,Finset.sum_mul]; simp_rw [Finset.mul_sum,Finset.smul_sum]; exact sum_congr rfl fun i _=> sum_congr rfl fun j _=> by rw [theta_smul,Matrix.smul_mul,Matrix.mul_smul,tells]; unfold priceWeight; simp only [mul_smul] -- scope implicit M
-- certification for straight studies (geometry using REAL t later); all Torus positives as below
private lemma compMark (a:Axis) (x:Cover)(p:wrap (CSide m B) x∈posY m B a)(t:Slot)(v: Ket SpinIdx):acts (cutM (matterSet (CSide m B) (posY m B a))) (pitch _ x R t v) = pitch _ x R t v:=by
 unfold pitch cantor; rw [map_smul,map_sum]; apply congrArg; apply sum_congr rfl; intro i _; unfold basisC; simp only [map_smul]; rw [cut_basis,if_pos]; rw [mem_matterSet]; exact p
variable (a:Axis)
private lemma leafUp (i:Personality)(x:Cover)(p:wrap (CSide m B) x∈posY m B a): Sector (matterSet (CSide m B) (posY m B a)) true (ton (player (CSide m B) x R i)):=by
 unfold player; cases w:i.down; exact Sector.makeP _ (compMark _ _ _ p _ _); change Sector _ _ (remove (-pitch _ x R i.color i.voice)); exact (Sector.makeP (-pitch _ x R i.color i.voice) (by rw [map_neg,compMark _ _ _ p])).contr -- tune `..`
private lemma costUp (C:List α)(p:∀ i∈ C,wrap (CSide m B) (Y i)∈ posY m B a):Sector (matterSet (CSide m B) (posY m B a)) (wheat C) (literal Y Z (CSide m B) R C):=by
 induction C with
 | nil=> simpa [wheat,literal,rollC] using (show Sector (matterSet (CSide m B) (posY m B a)) false 1 from Sector.one)
 | cons i C ih=> unfold literal rollC; rw [List.map_cons,List.prod_cons]; rw [wheat]; exact (leafUp R a _ _ (p i (by simp))).mul (ih (fun i l=>p i (List.mem_cons_of_mem _ l)))
lemma bookedUp(b:Bool)(η:∀ i:β,wheat (F i)=b)(p:∀ i,∀ x∈F i,wrap (CSide m B) (Y x) ∈ posY m B a): Sector (matterSet (CSide m B) (posY m B a)) b (utter Y Z (CSide m B) R F u):=by
 apply Sector.sumS; exact fun i _=> (show Sector _ b (literal Y Z (CSide m B) R (F i)) from η i ▸ costUp Y Z R a (F i) (p i)).scale _
-- convergence from reflected pose estimates actualν height & X geometry
variable (b:Bool) {N':ℕ→Side}{R':ℕ→ℝ}(Q: Agenda α R')(E:Agenda (α ⊕ α) R') (k: E.posV=Sum.elim (K ∘ X) X)(v:E.appointments=fun i=>posted M (Q.appointments i)) {j:ℕ}
local notation "ε" i:max=> utter (Q.appointments i) Z (N' i) (R' i) F u
include k v
lemma tendedCost(hj:1 ≤ j)(K':ℕ→Jill.Male)(Y':Yard N' R')(p:∀ i, Wave (Single (N' i))) (q:∀ᶠ i in atTop,Sea (latPose j (K' i) (N' i)) (p i)): Tendsto (fun i=> SpinPrice (p i) (poseX M b (ε i))) atTop (𝓝 (harvestCost M K X Z F u b)):=by
 simp_rw [runCost M, SpinPrice.pool,SpinPrice.cash]; unfold harvestCost; rw [←k]; refine tendsto_finsetSum _ fun i _=> tendsto_finsetSum _ fun l _=>?_ ; have ht:= wordPrice K' p Y' hj q E (Packed M Z) (couple (F i) (F l)); rw [v] at ht; exact ht.const_mul _
end YM.CF.Hygrometry
