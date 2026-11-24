import YM.CF.Sods.Zone
import YM.CF.Kea.Cool
import YM.CF.Matter.Mass
set_option autoImplicit false
noncomputable section
namespace YM.CF.Sods
open Function Filter Metric Finset Kea Lat Lattice Laurent Fir Rush Tulip Cube SU
open scoped Topology BigOperators Matrix ContDiff Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
abbrev Key:=Fin 5
abbrev Hat:=Axis→Key
def zCore:TF:=⟨fun i=>if i=(0:SU.F) then -4*(2*Real.pi/5) else 2*Real.pi/5,by norm_num [Fin.sum_univ_succ,F]⟩
lemma z_total:waveG zCore=central:=by
 have hp:pw (2*Real.pi/5)=SU.z:=by unfold pw BZ.phase SU.z; norm_cast; congr 1; push_cast; ring
 have hx:pw (-4*(2*Real.pi/5))=pw (2*Real.pi/5):=by
   unfold pw BZ.phase; push_cast; rw [show -(4:ℂ)*(2*Real.pi/5)*Complex.I=(2*Real.pi/5)*Complex.I- 2*Real.pi*Complex.I by ring,Complex.exp_sub,Complex.exp_two_pi_mul_I,div_one]
 apply group.mat_injective; change fund (waveG zCore)=_; rw [wave_id]; change Matrix.diagonal (pw ∘ zCore.val)=Matrix.diagonal _; congr 1; funext i; simp only [Function.comp_apply,zCore]; split_ifs<;>[exact hx.trans hp; exact hp]
lemma center_comm(i:Key)(x:E):central^i.val*x=x*central^i.val:=by
 have hp:Commute central x:=by
   unfold Commute SemiconjBy; apply group.mat_injective; refine (show Matrix.diagonal (fun i:F=> SU.z)*fund x=fund x*Matrix.diagonal (fun i:F=> SU.z) from ?_); ext a b; rw [Matrix.diagonal_mul,Matrix.mul_diagonal]; exact mul_comm ..
 exact hp.pow_left _
variable {N:Side}{d:Candle}
def welt(U:Bkg N)(x:Hat):Bkg N:= fun i=> (wob N (fun a=>central^(x a).val) i)*U i
lemma wok(U:Bkg N)(x:Hat): welt U x=wob N (fun a=>central^(x a).val)*U:=rfl
lemma w_g(U:Bkg N)(x:Hat)(f:Cart N):welt (Lattice.gauge f U) x=Lattice.gauge f (welt U x):=by
 funext ⟨i,a⟩; unfold welt Lattice.gauge wob; simp only; split_ifs; simp only [← mul_assoc,center_comm _ (f i)]; group -- ensure
lemma w_m(Q T:Bkg N)(k:ℝ)(h:lawnK Q T k)(U:Hat):lawnK (welt Q U) (welt T U) k:=by intro x; unfold welt; rw [cmp_left]; exact h x
def sun(d:Candle)(u:Hat)(N:Side):Candle:=fun i=>⟨(d i).val+(snapC zCore ((u i).val/(N.val:ℝ))).val,by simp only [Pi.add_apply,  sum_add_distrib, (d i).property,(snapC zCore _).property]; simp⟩
lemma dance (d:Candle)(u:Hat)(N:Side)(i): waveG ((sun d u N) i)^N.val=central^(u i).val * waveG (d i)^N.val:=by
 let t:=N.val; let k:ℝ:= t; let a:= u i; rw [←z_total,snap_p,snap_p,snap_p,tax_mul]; congr 1; apply Subtype.ext
 change k • ((d i).val+ ((a.val:ℝ)/k) • zCore.val)= _
 have hp:0<k:=nPos _; rw [smul_add,smul_smul, show k *(_/_)=(a.val:ℝ) by field_simp]; exact add_comm ..
def gKey(N:Side)(d:Candle)(u:Hat):Cart N:= (layout (Kea.tax (sun d u N) (N:=N)))⁻¹ * layout (Kea.tax d)
lemma overt(N:Side)(d:Candle)(u:Hat):Lattice.gauge (gKey N d u) (welt (Kea.tax d) u)=Kea.tax (sun d u N):=by
 let s:= sun d u N; let D:=Kea.tax d (N:=N); let X(a):=waveG (s a)^N.val; let A:=layout (Kea.tax s (N:=N)); have hp: welt (gauge (layout D) D) u = gauge A (Kea.tax s):=by
   unfold D A; rw [pacer,pacer]; funext ⟨i,a⟩; unfold welt wob; split_ifs <;> first| exact (dance d u N a).symm| simp
 unfold gKey; rw [← windy, ← w_g, hp]; change gauge A⁻¹ (gauge A _)=_; rw [windy,inv_mul_cancel,windy_u]
def slowT (N:Side)(d:Candle):Prop:=∀ a i,|(d a).val i|≤40*Real.pi/N.val
lemma slows (N:Side)(d:Candle)(x:speedB d N)(u:Hat):slowT N (sun d u N):=by
 intro a i; let n:ℝ:=N.val; have h:0<n:=nPos _; have ht: |zCore.val i| ≤ 4*(2*Real.pi/5):=by simp only [zCore]; split_ifs; rw [abs_of_nonpos (by have :=Real.pi_pos; nlinarith)]; ring_nf; simp; rw [abs_of_nonneg (by positivity)]; nlinarith [Real.pi_pos]
 change |_+((u a).val/n)*zCore.val i|≤_ -- annotate
 apply (abs_add_le ..).trans; rw [abs_mul]; have hx: (u a).val < 5:= (u a).isLt; have hy: |(u a).val/n| ≤ 5/n:=by rw [abs_of_nonneg (by positivity : 0 ≤ (u a).val/n)]; exact div_le_div_of_nonneg_right (by exact_mod_cast hx.le) h.le
 refine (add_le_add (x a i) (mul_le_mul hy ht (abs_nonneg _) (by positivity))).trans ?_; unfold n; have he:=Real.pi_pos; field_simp; nlinarith
end YM.CF.Sods
