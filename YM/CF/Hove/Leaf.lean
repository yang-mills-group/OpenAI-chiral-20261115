import YM.CF.Hove.Milk
import YM.CF.Hove.Visa
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Hove
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill

variable (j m:ℕ)(e:Even j)(p:4≤j)(v:2≤ m)
variable {c f :Side}(o:Site c)(G:Ratio c f)(w:Odd G.count.val)(T:Script Male)(u:Use j G.count T)(L:Op (Single f))(M:Male)
local notation "Sρ"=> (heel G o)
local notation "W"=> nook_T o m
local notation "φ"=> nook_T (heel G o) m
local notation "Zτ"=> paid_M
local notation "Ψ"=> chipF j G w T M (heel G o)
open Haro Branch Laic
variable {t:ℝ}(Y:cro G t)(P:Meter TailB G t)(Q:Meter Grave G t){a b A C a' c':ℝ}{l k n j':ℕ}(X:∀ i:TailB,Support (More f)→ Toll (Iota G))(pR:∀ i x,Suite (badge _) (pinH G t true) (pinH G t false) x (X i x) (P i x))(hk:∀ i,incline (hall G t) j' a' (fun _=>C) b (X i))(hc:0≤a')(hb:3*a≤b)(hp:0<a)(he:a ≤ 1)(h:0≤ C)
variable {ι:Type}(S_:ι→Male)(U:WG ι)(i:ι)(Po:∀ i n,U i n 1=0)(z:Y.val=1)(Hv:∀ b,Along j G.count w (Thread j) b (S_ i) G 1)(Hy:fulfills G w t (j:=j) S_ U i P Q Y)
local notation "Mρ"=> (mintY m (a:=a) (C:=C))
local notation "Δp"=> pulled G Y P L
local notation "tG"=> (Thread j) -- tune Use
local notation "ΣJ"=> totF j G w (Thread j) (S_ i)
include p e Po Hv Hy z
lemma ψ_Q : Δp univ = ΣJ L :=by
 let d(q:Bool)(x:Support (More f)):= openQ G Y P x q
 have he(q:Bool): (∑ i,d q i)=lensF G w (Thread j) j (!q) (S_ i):=by
    have ht:= hue j e (by omega) S_ U Po i G w Y P Q Hv z Hy q; rw [← show arch G (∑ i,P (true,q) i Y)=lensF G w (Thread j) j (!q) (S_ i) from ht]; ext a b; simp only [openQ,arch,d,Matrix.of_apply, Matrix.sum_apply]
 unfold pulled; simp_rw [← Matrix.mul_sum]; rw [← Matrix.sum_mul,←Matrix.sum_mul,←Matrix.conjTranspose_sum,he true, he false]; rfl
omit Po Hv Hy z
include v
lemma crest_H : ∃ A:ℝ,0<A ∧∀ {c f:Side}(o:Site c)(G:Ratio c f)(w: Odd G.count.val)(T:Script Male),Use j G.count @T →∀ (L:Op (Single f))(M:Male), paid_M o (totF j G w T M L-chipF j G w T M (heel G o) (domF (heel G o) L)) m ≤ A * paid_M (heel G o) L m / (G.count.val:ℝ)^5:=by
 obtain ⟨A,z,H⟩:= thrice j m e p v; refine ⟨A*(2:ℝ)^m,mul_pos z (by positivity),fun {c f} o G w T u L M=>?_⟩
 let F:= totF j G w T M L; let o':=heel G o; let K:= chipF j G w T M o' (domF o' L); have hx:= faith j G w T M o' L
 refine le_trans ?_ ((H G w T u M o' L).trans ((mul_le_mul_of_nonneg_left (limP o' L m) (by positivity)).trans_eq ?_)); swap; · ring
 unfold paid_M; rw [show nook_T o m=feeT G m o' from funext fun x=>cue_l G w o m x, show pinF (F-K)=pinF F-pinF K from rfl,hx]
-- transfer subset error combine. envelope API: paid_M dims unify Bru. choose macro constants H,K.
structure TendV (j m:ℕ) where
 A:ℝ
 C:ℝ
 hp:0 ≤ A
 ht:0 ≤ C
 pay:∀ {c f:Side}(o:Site c)(G:Ratio c f)(w: Odd G.count.val)(T:Script Male),Use j G.count @T→∀ (L:Op (Single f))(M:Male), paid_M o (totF j G w T M L-chipF j G w T M (heel G o) (domF (heel G o) L)) m ≤ A * paid_M (heel G o) L m / (G.count.val:ℝ)^5
 bench (b:Bool):∀ {c f:Side}(o:Site c)(G:Ratio c f)(w: Odd G.count.val)(T:Script Male),Use j G.count @T →∀ (M:Male)(n:ℕ),2*n<c.val→ BenchQ j G w M b o T C n
lemma thunder : Nonempty (TendV j m):=by obtain ⟨A,h,H⟩:= crest_H j m e p v; obtain ⟨C,hq,V⟩:= hall_Q j p e; exact ⟨A,C,h.le,hq,@H,fun b _ _ o G w T u M n v=> V G w M b o @T u n v⟩
-- exact op scaled Pt residual in calibrated chart, no labels normal. λ then
variable (J:Finset (Support (More f)))(hJ:∀ D:Support (More f),D∉J → l ≤ D.card)
include Po Hv Hy z w pR hk hc hb hp he h hJ
local notation "Ξ"=> domF (heel G o)
variable (V:TendV j m)
local notation "G_p"=> chipF j G w (Thread j) (S_ i) (heel G o) (Ξ L)
local notation "Sθ"=> (paid_M Sρ L m)
local notation "L₀"=> (G.count.val:ℝ)
local notation "Xl"=> (2*((2:ℝ)^m*Mρ l*Mρ 0)+ V.A/L₀^5)
include V
lemma cord : Zτ o (Δp J -G_p) m ≤ Xl * Sθ:=by
 have ht:= melt m o G w L Y P X pR hk hc hb hp he h J hJ; rw [ψ_Q j e p _ _ _ _ _ _ S_ U i Po z Hv Hy] at ht -- tune
 rw [show Δp J -G_p = (Δp J- ΣJ L)+(ΣJ L-G_p) from (by abel)]
 exact (paidp_sum ..).trans ((add_le_add ht (V.pay o G w (Thread j) (canUse j _ w) L (S_ i))).trans_eq (by ring))
end YM.CF.Hove
