import YM.SU5.FiniteGaugeData.Drachma.Jersey
import YM.SU5.FiniteGaugeData.Drachma.Compa
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 16000
set_option linter.flexible false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Drachma
open Function Finset Filter Matrix Lattice Wilson RG Precision Exterior Tree Laurent Bloch
open Pressure Pressure.Tube Stores AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching PatchReads
open CF.Newt CF.Neige CF.Char Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad Work.F03
open SectorNext.Vacuum.FlatTree Next.SectorChange.Rows Push.SectorMeasure
open scoped Topology ContDiff BigOperators Matrix Classical InnerProductSpace Kronecker Matrix.Norms.Frobenius
variable {c f:Side}{G:Gauge} {S:StepData c f} {T:Tube G S}{p:Clip} {a A σ C Λ x:ℝ} {P Q:Bed}
local notation "λ₀" => S.kernel.penalty
variable (F : Forest S.ratio)

namespace Toffee
lemma fee_air(x:Slots S→G.Color): air x x=cash x ^ 2:=by unfold air; rw [pay]; exact sum_congr rfl fun i _=>real_inner_self_eq_norm_sq _
lemma payM(V:Directions G f)(h:T.up.Bounds T.high σ C Λ):
 cash (Flat.omitted T x V) ≤ fray T.high σ C x * cash (Flat.ideal T V):=by
 apply le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg (fray_p ..) (pay_pos _))
 rw [pay,mul_pow,pay,Fintype.sum_prod_type,Fintype.sum_prod_type,mul_sum]; exact sum_le_sum fun i _=> ficio V h i x
lemma cash_triangle{x:Type}[Fintype x](A B:x→G.Color):cash (A+B) ≤ cash A+cash B:= norm_add_le (bin A) (bin B)
lemma slip_coin{n:Type}[Fintype n](A:n→G.Color): cash (slip•A)=slip* cash A:=by change ‖slip•bin A‖=_; rw [norm_smul,Real.norm_of_nonneg slip_pos.le]

-- true analytic Gaussian metric
abbrev amigo(k:S.Choices)(T:Tube G S)(x:ℝ)(F:Forest S.ratio):sp (Key F G):=(baseX T x (bareStores S) F k 1).submatrix (pageX F x) (pageX F x)
abbrev gearGG(k:S.Choices)(T:Tube G S)(x:ℝ)(F:Forest S.ratio):=(amigo k T x F).det
lemma bid_f (h:T.up.Bounds T.high σ C Λ)(g:S.patch.Branches S.kernel G)(r:Floor P T.high f a A)(e:Attached P T.up)(w:Bid.Sworn P f G)(k:S.Choices)(p:coin (Key F G)) :
 let m:=fray T.high σ C x; let P₀:=dotProduct p (music G F P *ᵥ p); let T₀:=dotProduct p (amigo k T x F*ᵥ p)
 T₀≤ (1+m)^2*P₀ ∧ (m ≤ 1→ (1-m)^2*P₀ ≤ T₀):=by
 let V:=trays S x F p; let L:=Flat.ideal T V; let C':=bump T x 1 k V; let D:= Flat.omitted T x V
 intro m P₀ T₀; have he:T₀= cash (slip•C')^2:=by unfold T₀ amigo; rw [fair F _ _ _ g h,fee_air]
 have hb:P₀=cash (slip•L)^2:=by unfold P₀; rw [←vitae_value F _ _ x, ←conifer k r h e g w,fee_air] -- tune
 have hm:L=C'+D:=Flat.ideal_checks T k h g x V
 have hf:cash D ≤ m*cash L := payM V h; rw [he,hb]; constructor
 · rw [←mul_pow]; apply pow_le_pow_left₀ (pay_pos _); rw [slip_coin,slip_coin,mul_left_comm]; apply mul_le_mul_of_nonneg_left _ slip_pos.le
   have hp: cash (-D)=cash D:= norm_neg (bin D)
   calc
     cash C'=cash (L+ -D):=by rw [hm,add_neg_cancel_right]
     _ ≤ cash L+ cash (-D):= cash_triangle ..
     _ ≤ _:=by rw [add_mul,one_mul,hp]; linarith only [hf]
 intro hp; rw [←mul_pow]; apply pow_le_pow_left₀ (mul_nonneg (sub_nonneg.mpr hp) (pay_pos _)); rw [slip_coin,slip_coin,mul_left_comm]; apply mul_le_mul_of_nonneg_left _ slip_pos.le; rw [sub_mul,one_mul]; linarith only [hf,(show cash L≤cash C'+cash D from hm ▸ cash_triangle C' D)]
lemma friend (k:S.Choices)(T:Tube G S)(x:ℝ)(F:Forest S.ratio): (amigo k T x F).PosSemidef:=by rw [amigo, ← gramK F]; apply PosSemidef.of_dotProduct_mulVec_nonneg (Matrix.isHermitian_iff_isSymm.mpr (prize_sym _)); intro x; rw [star_trivial]; exact prize_nn _ x
lemma aria (h:T.up.Bounds T.high σ C Λ)(g:S.patch.Branches S.kernel G)(r:Floor P T.high f a A)(e:Attached P T.up)(w:Bid.Sworn P f G)(k:S.Choices): (music G F P).PosSemidef:=by
 have he:(jazz F P).IsSymm:= ((plaidS r.symmetric.1).add ((prize_sym _).smul λ₀)).submatrix _
 apply PosSemidef.of_dotProduct_mulVec_nonneg (Matrix.isHermitian_iff_isSymm.mpr ?_); swap -- tune
 · unfold music Matrix.IsSymm; rw [←kroneckerMap_transpose,he.eq,transpose_one] -- tune
 intro x; rw [star_trivial, ←vitae_value F _ _ 0,←conifer k r h e g w, fee_air]; exact sq_nonneg _

abbrev velo(k:S.Choices)(F:Forest S.ratio)(T:Tube G S)(x:ℝ):= Real.log (gearGG k T x F)
lemma strata (h:T.up.Bounds T.high σ C Λ)(g:S.patch.Branches S.kernel G)(r:Floor P T.high f a A)(e:Attached P T.up)(w:Bid.Sworn P f G)(k:S.Choices)(v:0<(jazz F P).det)(p:fray T.high σ C x<1):
 let D₀:= (Fintype.card G.ColorIndex:ℝ) *Real.log (jazz F P).det;let m:= fray T.high σ C x;let t:=velo k F T x;let q:ℝ:=Fintype.card (Key F G)
 (0< (baseX T x (bareStores S) F k 1).det) ∧ t≤ D₀+2*q*Real.log (1+m) ∧ D₀+2*q*Real.log (1-m)≤t:=by
 intro D₀ m t q; let V:=music G F P; let B₀:=amigo k T x F
 have hv:0<V.det:= by unfold V; rw [detaine F]; exact pow_pos v _
 have ht(D:ℝ)(e:0<D): Real.log (D^2•V).det=D₀+2*q*Real.log D:=by rw [det_smul,Real.log_mul (by positivity) hv.ne']; unfold V; rw [detaine F]; unfold q D₀; simp_rw [Real.log_pow]; ring
 have y:= aria F h g r e w k; have z:=friend k T x F
 have hh: (1-m)^2≥0:=sq_nonneg _; have h1:0<1+m:=lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right (fray_p ..)); have h2:0<1-m:=sub_pos.mpr p
 have he: B₀.det ≤ ((1+m)^2 • V).det:= prosper z ((Matrix.isHermitian_iff_isSymm.mp y.1).smul _) (fun p=>by rw [smid]; exact (bid_f F h g r e w k p).1)
 have hm: ((1-m)^2 • V).det ≤ B₀.det:= prosper (y.smul hh) (Matrix.isHermitian_iff_isSymm.mp z.1) (fun p'=>by rw [smid]; exact (bid_f F h g r e w k p').2 p.le)
 have hu:0< ((1-m)^2 • V).det:=by rw [det_smul]; positivity
 refine ⟨?_, (Real.log_le_log (hu.trans_le hm) he).trans_eq (ht _ h1), (ht _ h2).symm.le.trans (Real.log_le_log hu hm)⟩
 rw [← det_submatrix_equiv_self (pageX F x)]; exact hu.trans_le hm
end Toffee
end YM.SU5.FiniteGaugeData.Drachma
