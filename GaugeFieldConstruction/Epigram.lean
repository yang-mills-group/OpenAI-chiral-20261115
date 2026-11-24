import GaugeFieldConstruction.Hurrah
import YM.SU5.FiniteGaugeData.Crest.Alps
import YM.CF.Ember.Bud
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vale.Veins
open Function Filter Lattice Laurent Bloch Wilson Precision RG Next.Free Work.F08 Craft Pressure Stationary Tree Reef Hom AnalyticBridge.LocalGaussianLaws
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.Frobenius
open Exterior Next.Free.Stretch Finset Matrix
variable {c f:Side}
abbrev face_K (a:Cover × PlaqAxes) (c:Side): form 1 c:= (d 1 c)ᵀ *ᵥ Pi.single (wrap c a.1,plaquette a.2) (1:ℝ)
lemma test_lit (b:Cover × PlaqAxes) (v:Body 1 c→ℝ):let x:=wrap c b.1; let i:=b.2.val.1; let j:=b.2.val.2;(face_K b c) ⬝ᵥ v=v (x+step i, coord j)-v (x,coord j)-(v (x+step j, coord i)-v (x,coord i)):=by
 intro x i j; unfold face_K; rw [mulVec_transpose,← dotProduct_mulVec]; unfold dotProduct; simp only [Pi.single_apply,ite_mul,one_mul,zero_mul,sum_ite_eq',mem_univ,↓reduceIte]; exact d_plaquettes .. -- tune
lemma test_glow (b:Cover × PlaqAxes)(v:Body 1 c →ℂ):let x:=wrap c b.1; let i:=b.2.val.1; let j:=b.2.val.2;reK (face_K b c) ⬝ᵥ v=v (x+step i, coord j)-v (x,coord j)-(v (x+step j, coord i)-v (x,coord i)):=by
 intro x i j; apply Complex.ext
 · simpa [dotProduct,reK,Complex.mul_re,Complex.re_sum] using test_lit b fun i=> (v i).re
 simpa [dotProduct,reK,Complex.mul_im,Complex.im_sum] using test_lit b fun i=> (v i).im
lemma test_bay (b:Cover × PlaqAxes)(x:Body 1 c)(p:face_K b c x≠0): separation (wrap c b.1) x.1≤1:=by
 let i:= b.2.val.1; let j:=b.2.val.2; let o:= wrap c b.1; let v:form 1 c:=Pi.single x 1
 have he: (face_K b c) ⬝ᵥ v=face_K b c x:=by simp [v,dotProduct,Pi.single_apply,mul_ite]
 rw [←he,test_lit] at p
 have ht(a:Axis): separation o (o+step a) ≤1:=by rw [separation_comm,separation,add_sub_cancel_left]; exact pdist_step a
 by_contra w; have hZ:separation o o≤1:=by simp [separation,pdist,Lattice.lift]
 have hh(a: Site c)(b:TypeFace 1)(p:separation o a≤1):v (a,b)=0:= Pi.single_eq_of_ne (show (a,b)≠x from fun V=>w (by rw [←V]; exact p)) _
 rw [hh _ _ (ht _),hh _ _ hZ,hh _ _ (ht _),hh _ _ hZ] at p; simp at p
lemma test_gap {a b:Cover × PlaqAxes}(u:42<separation (wrap c a.1) (wrap c b.1)): Crossed (face_K a c) (face_K b c):=by
 intro x y t h; have v:= test_bay a x t; have w:=test_bay b y h; rw [separation_comm] at w
 have hi:=separation_triangle (wrap c a.1) x.1 y.1; have he:=separation_triangle (wrap c a.1) y.1 (wrap c b.1); omega
abbrev creditW (a:Cover × PlaqAxes)(p:Momentum)(r:TypeFace 1):ℂ:=let i:=a.2.val.1; let j:=a.2.val.2; mode p a.1*((if coord j=r then chip (p i) else 0)- (if coord i=r then chip (p j) else 0))
lemma spell (a:Cover × PlaqAxes)(p:Site c): PriceM (face_K a c) (mon p)=creditW a (mon p):=by
 funext r; let q:=mon p; unfold PriceM; rw [test_glow]; unfold perQ creditW; simp only
 have he(z:Site c):mode (mon p) (lift z)=Bloch.cell p z:=rfl
 simp_rw [he,cell_add,cell_wrap,cell_step]; unfold chip; split_ifs <;> ring
lemma credit_phase (a:Cover × PlaqAxes)(p:Momentum)(v:Cover)(r:TypeFace 1): creditW a (p+ reciprocal v) r = creditW a p r:=by unfold creditW; simp only [Pi.add_apply,mode_phase,mode_periodic,mul_one,reciprocal,chip_repeat]
lemma resume (a:Cover × PlaqAxes)(r:TypeFace 1):Continuous (fun p:Momentum=>creditW a p r):=by
 unfold creditW; simp only; split_ifs <;> unfold mode <;> try unfold chip
 all_goals fun_prop
abbrev cli (p: Momentum) := Real.sqrt (lengthSq p)
lemma cli_sq (p:Momentum) : cli p ^2=lengthSq p:=Real.sq_sqrt (by unfold lengthSq; positivity)
lemma chipQ (b:Cover × PlaqAxes)(p:Momentum)(he:p∈baseCube)(a:TypeFace 1): ‖creditW b p a‖≤ (meter.high+meter.high)*cli p ∧ ‖creditW b p a‖≤4:=by
 have hg(i:Axis): ‖chip (p i)‖ ≤ meter.high * cli p:=by
    apply (meter.above _ (zone_in_disk _ (mem_cube_real (base_subset_realCube zone_pos he) zone_pos) i)).trans; apply mul_le_mul_of_nonneg_left _ meter.high_pos.le
    have hb:‖p i‖^2 ≤ lengthSq p:=single_le_sum (f:=fun i=>‖p i‖^2) (fun i _=>sq_nonneg _) (mem_univ _); rw [← cli_sq] at hb; have hz:0≤cli p:= Real.sqrt_nonneg _; nlinarith [norm_nonneg (p i)]
 have hd(i:Axis): ‖chip (p i)‖≤2:=by unfold chip; apply (norm_sub_le ..).trans; rw [← Exterior.factor]; simp [mode_real _ _ he.1]; norm_num
 unfold creditW; simp only [norm_mul,mode_real _ _ he.1,one_mul]; let i:=b.2.val.1; let j:=b.2.val.2
 have hp:0 ≤ meter.high*cli p:= mul_nonneg meter.high_pos.le (Real.sqrt_nonneg _)
 rw [add_mul]
 constructor <;> apply le_trans (norm_sub_le ..) -- tune <;>
 · apply add_le_add <;> split_ifs <;> first | apply hg | rwa [norm_zero]
 have hk: (2:ℝ)+2=4:=by norm_num
 rw [←hk]; apply add_le_add <;> split_ifs <;> first | apply hd | simp -- tune
open CF.Crest CF.Crest.Shore -- income
abbrev fenceW (a:Cover × PlaqAxes)(p:Momentum)(b:Side)(l: Site b) := BridgeT p b (creditW a p) l
lemma receipts_B (a:Cover × PlaqAxes)(p:Momentum)(b:Side)(l:Site b)(r:TypeFace 1): fenceW a p b l r=(area b (aliasAt p l))^4*rail b (aliasAt p l (axisEquiv.symm r))*creditW a p r:=by unfold fenceW BridgeT FilterT; field_simp [side_ne b] -- tune
abbrev gateW (a b:Cover × PlaqAxes)(p:Momentum)(L:Side)(l:Site L)(r:TypeFace 1):ℂ:= (divisor L (L.val • aliasAt p l))⁻¹ * (fenceW b p L l r * star (fenceW a p L l r))
lemma remits (a b:Cover × PlaqAxes)(p:Site c)(L:Side)(l:Site L): WaveT (face_K a c) (face_K b c) L (mon p) l=∑ i:TypeFace 1,gateW a b (mon p) L l i:=by unfold WaveT; dsimp only; rw [spell,spell,dotProduct,mul_sum]; rfl
end YM.CF.Vale.Veins
end
