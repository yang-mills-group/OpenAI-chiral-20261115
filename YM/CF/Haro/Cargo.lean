import YM.CF.Haro.Mint
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Haro
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill
variable {c f:Side}(G:Ratio c f)(h: Odd G.count.val)
open Branch Laic
variable {t:ℝ}(p:0<t)(Y: cro G t)(W: Meter TailB G t)
open Skye Precision
open Jet Scree
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{z:E}{n:ℕ}{K u v w A' B' C':ℝ}
-- crack total equals literal fee for PH slice. 
variable {P B: RG.BudgetPoint}(k:Finset (Dwell f)→ℝ)(x:ℝ)(o: Seat f)
abbrev tray {f:Side}(i j:Single f): Finset (Dwell f):={ (true,i),(false,j)}
lemma tray_in {c:Side}:Injective fun i:Single c× Single c=>tray i.1 i.2:=by
 rintro ⟨i,j⟩ ⟨x,y⟩ h; have hv : ∀ a:Dwell c,a∈ tray i j↔a∈tray x y:= Finset.ext_iff.mp h; have hx:(true,i)∈ tray x y:=(hv _).mp (mem_insert_self ..); have hp:(false,j)∈ tray x y:=(hv _).mp (by simp [tray]); simp only [tray,mem_insert,mem_singleton,Prod.mk.injEq, Bool.false_eq_true,true_and,Bool.true_eq_false,false_and,or_false,false_or] at hx hp; exact Prod.ext hx hp
abbrev sheet (V:Finset (Dwell f)):=Scree.tariff P o x V * k V
lemma pay_j (k':∀ i,0 ≤ k i)(hp:0 ≤ x):
    ∑ i:Prism.Rock f,∑ j:Prism.Rock f, amt P.power o i j*x^2*Prism.crack k i j≤ ∑ i:Finset (Dwell f),sheet (P:=P) k x o i:=by
 let F:=sheet (P:=P) k x o; apply le_trans ?_ (sum_le_sum_of_subset_of_nonneg (s:=univ.image (fun i:Single f×Single f=>tray i.1 i.2)) (t:=univ) (f:=F) (subset_univ _) (fun i _ _=>mul_nonneg (by unfold Scree.tariff; positivity) (k' i))); conv_rhs=> rw [sum_image (tray_in.injOn), Fintype.sum_prod_type, Fintype.sum_prod_type]
 apply sum_le_sum; intro i _; unfold Prism.crack; simp_rw [Finset.mul_sum]; rw [sum_comm]; refine sum_le_sum fun a _=>?_ ; conv_rhs=> rw [Fintype.sum_prod_type]
 apply sum_le_sum; intro j _; apply sum_le_sum; intro b _; apply le_of_eq; unfold F sheet tray; rw [rope P.power o i j a b x P rfl]
-- fiscal precise every geometry charge
abbrev flavor:ℝ:=(Fintype.card Slot:ℝ)
variable {v' b b' d C':ℝ}(Y Z: Support (More f)→ Toll (Iota G))(y:∀ i,Y i≥0)(g:∀ i,Z i≥0)
include y g h
lemma beak (w:0 ≤ v')(pv:0 ≤ b)(qu:incline (hall G t) P.power (G.count.val:ℝ)⁻¹ (fun _=> u) b Y)(zu:incline (hall G t) P.power (G.count.val:ℝ)⁻¹ (fun _=> v) b Z)(a:∀ i,0≤k i)(r s:Prism.Rock f): let U':= flavor*u; let V':= flavor*v; (∑ i:Prism.Rock c,∑ j:Prism.Rock c,∑ F: Support (More f),∑ X:Support (More f), (1+wheel_l n)* θ_I n (horn*paintL G r i (Y F)) (horn*Prism.crack k r s) (horn*paintL G s j (Z X))*v'* (amt P.power ((ratio G).parent o) i j*x^2))≤
 (1+wheel_l n)* θ_I n (horn*U') (horn*(amt P.power o r s*x^2*Prism.crack k r s)) (horn*V')*((3:ℝ)^P.power*v'):=by
 intro F X; -- tune
 let hz(i:Prism.Rock c):= ∑ v:Support (More f),pactB G P.power r i*paintL G r i (Y v); let H(j:Prism.Rock c):= ∑ v:Support (More f),pactB G P.power s j*paintL G s j (Z v)
 have hu:∑ i:Prism.Rock c,hz i≤F:= hK G h Y y qu pv r; have hv:∑ i:Prism.Rock c,H i≤X:=hK G h Z g zu pv s
 let L(A B:ℝ):=(1+wheel_l n)* θ_I n (horn*A) (horn*(amt P.power o r s*x^2*Prism.crack k r s)) (horn*B)*((3:ℝ)^P.power*v'); let c:=L 1 1
 have he(x y): L x y=c*(x*y):=by unfold c L θ_I; ring
 have hb:0≤horn:=zero_le_one.trans Haro.p0; have hb1:0 ≤ Haro.pole:=zero_le_one.trans Haro.p1; have hx:0 ≤ wheel_l n:=zero_le_one.trans Haro.wheels_p
 have hW:0 ≤ amt P.power o r s:=by unfold amt; positivity
 have hu'(A B v):=gust_l G Y A B v y; have hv'(A B v):=gust_l G Z A B v g; have hp:0≤Prism.crack k r s:=sum_nonneg fun i _=>sum_nonneg fun j _=>a _
 have ht:0 ≤ c:=by unfold c L θ_I; positivity; -- error c shadow side! rename
 refine le_trans ?_ ((mul_le_mul_of_nonneg_left (mul_le_mul hu hv (by unfold H pactB; apply sum_nonneg; intro i _; apply sum_nonneg; intro j _; exact mul_nonneg (by positivity) (hv' ..)) ?_) ht).trans_eq (he _ _).symm)
 swap; · apply le_trans _ hu; apply sum_nonneg; intro i _; apply sum_nonneg; intro z _; exact mul_nonneg (by unfold pactB; positivity) (hu' ..)
 conv_rhs=> rw [sum_mul,Finset.mul_sum]; 
 apply sum_le_sum; intro i _; conv_rhs=> rw [Finset.mul_sum, Finset.mul_sum]
 apply sum_le_sum; intro j _; conv_rhs=> rw [show hz i= _ from (rfl : hz i=∑ v:Support (More f),pactB G P.power r i *paintL G r i (Y v)),sum_mul,mul_sum]
 apply sum_le_sum; intro T _; conv_rhs=> unfold H; rw [Finset.mul_sum,Finset.mul_sum]
 apply sum_le_sum; intro A _
 let Z':=(1+wheel_l n)* θ_I n (horn*paintL G r i (Y T)) (horn*Prism.crack k r s) (horn*paintL G s j (Z A))*v'; refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (amtV G o r s i j P.power) (sq_nonneg x)) (show 0≤ Z' from by unfold Z' θ_I; have hx:= hu' r i T; have hp':=hv' s j A; positivity)).trans_eq ?_
 unfold Z' c L θ_I; ring -- tune
end YM.CF.Haro
