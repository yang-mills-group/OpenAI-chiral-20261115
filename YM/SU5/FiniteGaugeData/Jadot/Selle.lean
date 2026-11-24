import YM.SU5.FiniteGaugeData.Jadot.Farm
import YM.SU5.FiniteGaugeData.CodaT.Print
/-! # Actual ledger assembly. -/
set_option autoImplicit false
set_option synthInstance.maxSize 22000
set_option maxHeartbeats 550000
set_option linter.flexible false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Cuprite.Spirit
open Function NormedSpace Filter Finset MeasureTheory Lattice RG Wilson AnalyticBridge Metric Pressure Galope CF CF.Pastry CF.Py CF.Py.Rate
open SU Fock Reduction Reduction.Jersey Reduction.Drama Reduction.Drama.Pack Reduction.Hutch Cube Lat Window Presidio Tenant Skye Scree Graph CF.Buffered Window.Brique Next.Rank Nacre -- amb.Supply
open Rush Scroll Peaks Tap Tulip Fir Cascade Dial Spire Paige Vault
open Avenue RouteM Spindle
open Rhythm Pilot PhaseM Steve VolumeRate
open scoped Topology ContDiff BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Kronecker ComplexOrder Classical
attribute [local instance] opCStarAlgebra
open Reduction.Dinar Reduction.Dijon Reduction.Rheims Fock.Brique Reduction.Dijon.Currency Reduction.Celeste Window.Presidio
open Reduction.Loyd Reduction.Loyd.Art Window.Presidio.Nigra Window.Presidio.Gato Fock.Relief Turnist
open Moorend YM.SU5.FiniteGaugeData.CodaT
namespace Alts
variable {n:Side} {X:Pane n}{P D L Q:Op (Single n)}{c b s a t k C ξ G α δ μ β v' ε' w' v:ℝ}{j m i w l d:ℕ}{S T R:Support (More n)} {U:Loom n}
local notation "Θ_"=> tickA n
local notation "Ν"=> Single n
local notation "Μ0"=> modesIn n
abbrev investK (m:ℕ):= m* Fintype.card (SpinIdx × SU.Slot)
abbrev investZ (m d:ℕ):= investK (m*(d+d+1)^4)
lemma knode(S:Support (More n)) : (modesIn n S).card ≤ investK S.card:=by
 let T:=modesIn n S; let J(i:T) : S × SpinIdx × SU.Slot := (⟨node i.val.1.1,(modes_at ..).mp i.property⟩, i.val.1.2,i.val.2)
 change T.card ≤_; unfold investK; rw [← Fintype.card_coe T,← Fintype.card_coe S, ←Fintype.card_prod]; apply Fintype.card_le_of_injective J; intro i j v; exact Subtype.ext (Prod.ext (Prod.ext (needle (congrArg (fun i:S×SpinIdx×SU.Slot=> i.1.val) v)) (congrArg (fun i=>i.2.1) v)) (congrArg (fun i=> i.2.2) v))
lemma snout (h:S.card ≤ m) : (modesIn n S).card ≤ investK m:= (knode S).trans (Nat.mul_le_mul_right _ h)
lemma tagZ(h:S.card≤ m): (modesIn n (Lattice.halo d S)).card ≤ investZ m d := snout ((Lattice.Corona.halo_size ..).trans (Nat.mul_le_mul_right _ h))
local notation "ℍ"=> (Lattice.halo : ℕ→Support (More n)→Support (More n))
structure Emblem (n:Side)(P:Op (Single n))(m d:ℕ)(t s k C ξ G:ℝ) where
 S:Support (More n)
 existsS : S.Nonempty
 pays: S.card≤ m
 span : radiusE S d
 X: Pane n → FC (Single n)
 stocked(u:Pane n):Art (Bar s (investK m)) (tickA n) (modesIn n S) false (X u) k
 colored(g:Mosquito n)(U:Pane n): X (gauge g U) = twist (quantU (tradew n g)) (X U)
 rough(Z:Pane n) : (Volt (tickA n) P (X Z)).re≤ ξ+G
 soaks(Z:Pane n)(p:fieldR S t Z): (Volt (tickA n) P (X Z)).re ≤ ξ+C
namespace Emblem
variable (A:Emblem n P m d t s k C ξ G)
-- padding via halo.M.Sha stamping
abbrev rep(l j:ℕ):= Lattice.halo j (Lattice.halo l A.S)
abbrev logoW (z:ℝ): Mark n:= fun i=> ((Real.exp z:ℝ):ℂ) • (1 + A.X i.1)
-- monot footprint & orientations. unique color pressure at shared frame.
section
variable (y:Fable P (tickA n))(a:Axis)(z:ℤ)
local notation "Gδ"=> carR a z n
local notation "M"=> twist (carR a z n)
local notation "p₀"=> Buffered.plane a z
local notation "Z"=> refF n a z
local notation "Fφ"=> fling a z n
private lemma drydock {X:Pane n}(h:fieldR (Z R) t X): fieldR R t (Fφ X):=by
 let N:=(p₀).anon n
 rintro ⟨x,i⟩ hx hy
 let v:= (Signed.mirror a); let b:Site (More n):=wrap _ (2 • (z • step a))
 let T:=(posDir i).rotate v
 have hb : N x∈ Z R := Finset.mem_image_of_mem N hx
 have he : N (x+step i) ∈ Z R := Finset.mem_image_of_mem N (a:=x+step i) hy
 have hw : N (x+step i)=N x+T.vec := by
    change affine v b (x+step i)=affine v b x+ ((posDir i).rotate v).vec; rw [Lattice.Step.vec_rotate, Lattice.Step.vec_pos, affine,affine,v.act_add, add_right_comm]
 rw [hw] at he
 change SU.group.chord (T.read X (N x))≤t
 cases hq:T with| mk i0 u=>
 rw [hq] at he; cases u
 · exact h (N x,i0) hb he
 change SU.group.chord (X (N x-step i0,i0))⁻¹ ≤ t
 have hx : N x-step i0 ∈ Z R := by simpa only [show (⟨i0,true⟩ : Lattice.Step)=negDir i0 from rfl, Lattice.Step.vec_neg, sub_eq_add_neg] using he
 rw [SU.group.chord_inv]; exact h (N x-step i0,i0) hx (by change N x-step i0+step i0 ∈ _; rw [sub_add_cancel]; exact hb)
private lemma signCode(v:Pane n)(g:Mosquito n): Fφ (Lattice.gauge g v)=Lattice.gauge (g ∘ (p₀).anon n) (Fφ v):= Push.Local.pull_gauge (Signed.mirror a) (wrap _ (2 • (z • step a))) v g
include y
lemma voltTurn(U:Pane n):(Volt (tickA n) P (theta Gδ (A.X U))).re=(Volt (tickA n) P (A.X U)).re:=by rw [Celeste.voltRefl y.tender _ (y.turn ..) (y.flip ..)]; rfl
def outward (a:Axis)(z:ℤ)(y:Fable P (tickA n)) : Emblem n P m d t s k C ξ G where
 S:=refF n a z A.S
 existsS:=A.existsS.image _
 pays:= card_image_le.trans A.pays
 span i u j v:=by
    obtain ⟨i,s,rfl⟩:=mem_image.mp u; obtain ⟨j,w,rfl⟩:=mem_image.mp v; unfold Shape.anon affine; rw [separation_translate,separation_signed]; exact A.span i s j w
 X U:= theta (carR a z n) (A.X (fling a z n U))
 colored g U:=by rw [signCode,A.colored]; exact theta_twist_right _ _ _ (congrArg Subtype.val (Lifted.gaugeSquare a z n g)) (sameRoom (A.stocked _)) -- params
 stocked U:= (A.stocked _).reflectX (carR a z n) (by have p:=y.turn a z; rw [map_sub,map_one] at p; nth_rw 2 [←p]; abel) (refl_modes a z _) -- tune shadow
 rough Z_:= (voltTurn A y a z _).trans_le (A.rough _)
 soaks Z_ t:= (voltTurn A y a z _).trans_le (A.soaks _ (drydock a z t)) -- hearth local includes duplicate variables.Needs procedure for z binder
lemma outlook (c:ℝ): reflMark a z (logoW A c)= logoW (outward A a z y) c:=by
 funext x; let U:=carR a z n; let f:= (Real.exp c:ℂ); change theta U (f • (1+_))=f • (1+_); rw [theta_smul,theta_add,theta_one,show star f=f from Complex.conj_ofReal _]; rfl
lemma sunrise(l j:ℕ): rep (outward A a z y) l j= Z (rep A l j):=by unfold rep; change ℍ j (ℍ l (Z A.S))= Z _; let X:=ℍ l A.S; have he:Z (ℍ j X)=ℍ j (Z X):= Fock.Brique.reflect_halo a z _ _; rw [← (show Z (ℍ l A.S)=ℍ l (Z A.S) from reflect_halo a z _ _), he]
end
end Emblem
/-- Emblem passport. count earned before geometry. -/
inductive Flush (P:Op (Single n)) (m d l r:ℕ)(t s k C ξ G α:ℝ): ℕ→ Support (More n)→ Mark n→Prop
 | piece(A:Emblem n P m d t s k C ξ G): Flush P m d l r t s k C ξ G α 1 (Emblem.rep A l r) (Emblem.logoW A α)
 | unit(V:Support (More n)): Flush P m d l r t s k C ξ G α 0 V 1
 | both {n₀ n₁:ℕ}{S T:Support (More n)}{x y:Mark n}: Flush P m d l r t s k C ξ G α n₀ S x → Flush P m d l r t s k C ξ G α n₁ T y→ Disjoint S T→ Flush P m d l r t s k C ξ G α (n₀+n₁) (S∪T) (x*y)
 | expand {k₀:ℕ}{S T:Support (More n)}{x:Mark n}: Flush P m d l r t s k C ξ G α k₀ S x→S⊆T→ Flush P m d l r t s k C ξ G α k₀ T x
namespace Flush
variable {x y:Mark n}
local notation "K₀"=> Flush P m d l j t s k C ξ G α
lemma flipL (H:Flush P m d l j t s k C ξ G α i S x) (O:Fable P (tickA n))(a:Axis)(z:ℤ): Flush P m d l j t s k C ξ G α i (refF n a z S) (Buffered.reflMark a z x):=by
 induction H with
 | piece A=> rw [A.outlook O,←A.sunrise O]; exact Flush.piece (A.outward a z O)
 | unit=> rw [show reflMark a z (1:Mark n)=(1:Mark n) from funext (fun i=>theta_one _)]; exact Flush.unit _
 | @both n m V T x y p q D e f=>
    have h:= Finset.disjoint_image (s:=V) (t:=T) (show Injective ((Buffered.plane a z).anon _) from (show Involutive ((Buffered.plane a z).anon _) from fun i=> fling_there a z i).injective)
    rw [refF,image_union,show reflMark a z (x*y)=reflMark a z x*reflMark a z y from funext (fun i=>theta_mul _ _ _)]; exact Flush.both e f (h.mpr D)
 | expand x p H =>exact Flush.expand H (image_subset_image p)
end Flush
end Alts
end YM.SU5.FiniteGaugeData.Cuprite.Spirit
