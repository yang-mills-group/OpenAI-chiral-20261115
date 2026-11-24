import GaugeFieldConstruction.Yucatan
set_option autoImplicit false
set_option maxHeartbeats 120000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.GaugeFieldConstruction.Wick.Yacht.Vesper
open StressFHeat MeasureTheory Analysis Function Filter Metric Maxwell Finset Gap Complex Cauchy Row Phys Flux.One Lamp Conj
open Lattice CF CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart CF.XGarden.MastTin.ArtCart.Violets CF.Py.Rate.LocalLimit.Papal
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
open HopeC CF.Buffered CF.Buffered.Lifted FlightFlux Fluxim TableF TableF.Lenten Layout Shield
-- canonical Pen coupon.Color.At
variable {α β:Type*}
lemma tested (i:α)(j:β)(u:J α)(v:J β):Phys.test (i,j) (times' u v)=Phys.test i u*Phys.test j v:=by
 have ht:test (i,j)= productRead (Phys.test i) (Phys.test j):= ket_ext fun ⟨t,v⟩=>by rw [← Cauchy.takes t v, read_times,Cauchy.takes]; by_cases e:t=i<;>by_cases p:v=j<;>simp [ket,Phys.test,Finsupp.single_apply,e,p]
 rw [ht]; exact read_times ..
lemma topK (i:α)(j:β)[DecidableEq β](b:β)(v:J α):test (i,j) (atop b v)=if b=j then test i v else 0:=by change test (i,j) (times' v (ket b))=_; rw [tested]; split_ifs with e <;> simp [test,ket,Finsupp.single_apply,e]
abbrev ballG (a:Wα)(j:Pen):ℝ:= (E_G j.1).val a.2.1.val.1 a.2.1.val.2 * Phys.dye j.2 a.2.2
abbrev boilG (i:Wα)(x:Cover)(j:Pen):ℝ:= faceT (E_D j.1) i.2.1.val.1 i.2.1.val.2 (i.1-x) * Phys.dye j.2 i.2.2
lemma hue_s (i j:Pig): dye i j= if j=i then 1 else 0:=by simp [dye, EuclideanSpace.basisFun_apply] -- tune
lemma seekP (i:Wα)(j:Pen): test j (pinG i)=(ballG i j:ℂ):=by
 rw [← Prod.eta (p:=j)]; unfold pinG debtG sectionG; rw [topK]; unfold ballG; rw [hue_s]; by_cases e:i.2.2=j.2<;> simp [e]; exact portal j.1 _ _ -- tune
lemma shadeD (i:Wα)(j:Pen)(d:Axis): test j (lace d (pinG i))= (((E_D j.1).val d i.2.1.val.1 i.2.1.val.2 * dye j.2 i.2.2:ℝ):ℂ):=by
 rcases j with ⟨a,b⟩; unfold pinG debtG sectionG lace; rw [← Phys.here,topK,hue_s b i.2.2]; by_cases p:i.2.2=b <;> simp [p]; exact portion ..
lemma boom (D:Axis→Module.End ℂ (J α))(i:J α)(K:HopeC E4): boon D i K 1=∑ k:Axis,(meanH K k:ℂ) • D k i:=by
 unfold boon; simp_rw [tower]; let P:Axis × Φ 0≃Φ 1:= Fin.consEquiv (fun _=> Axis); rw [← Equiv.sum_comp P (fun j:Φ 1=> (∫ u,(dock u j:ℂ)∂K.μ) • D (j 0) i),Fintype.sum_prod_type]; apply sum_congr rfl; intro j _; rw [Fintype.sum_unique]; unfold P Fin.consEquiv; simp only [Equiv.coe_fn_mk, Fin.cons_zero]; simp_rw [dock]; simp; rw [meanH, show (∫ u:E4,(u j:ℂ)∂K.μ)= ↑(∫ u:E4,u j ∂K.μ) from integral_ofReal (μ:=K.μ) (f:=fun x:E4=> x j),Complex.coe_smul] -- tune
lemma topView (i:Wα)(d:Pen)(x:Cover): test d (boon lace (pinG i) (Glint x i) 1)=(boilG i x d:ℂ):=by
 rw [boom,map_sum]; simp_rw [map_smul,smul_eq_mul, shadeD]; unfold boilG faceT; push_cast; rw [sum_mul]; apply sum_congr rfl; intro j _; rw [star_Y]; simp only [smul_eq_mul,Complex.ofReal_mul]; ring -- tune
variable (n:Side)(x:Cover)(p:StampSet n x)(i:Pen) (w:300<n.val)
local notation "aZ"=>Wasp n x p
local notation "oX"=>Θk n x
open AnalyticBridge VerifiedReset Skye Cube Push.SectorMeasure Work.F03 Wilson
lemma sam_K: separation (p.1.val).1 oX≤24:=by
 rw [separation_comm]; have hx:=seat_e x p; simpa only [knotX,halo_spec,mem_singleton,exists_eq_left] using hx
include w
lemma ΨK (b:ℝ): cast_P oX (gateC oX b (hem (E_G i.1) (dye i.2))) p= b*ballG aZ i:=by
 change toga (p.1.val) (gateC oX b _) p.2 = _; change faceCurl (p.1.val) (mapCo (plot oX (formC _) b)) p.2=_; rw [show (p.1.val)=((p.1.val).1,(p.1.val).2) from rfl,liaison_h (v:=(p.1.val).1) (b:=(p.1.val).2),formC_flux]; -- tune
 · change b * ((E_G i.1).val (p.1.val).2.val.1 (p.1.val).2.val.2 * dye i.2 p.2)=_; rfl
 · have ht:=sam_K n x p; change _ < n.val*2; omega
 change 10≤ n.val*2; omega
lemma ΨJ (b:ℝ): cast_P oX (gateT oX b (loomH (E_D i.1) (dye i.2))) p=b*boilG aZ x i:=by
 change toga (p.1.val) (gateT oX b _) p.2=_; change faceCurl (p.1.val) (mapCo (plot oX (formT _) b)) p.2=_; rw [show (p.1.val)=((p.1.val).1,(p.1.val).2) from rfl,liaison_h (v:=(p.1.val).1) (b:=(p.1.val).2),formT_flux]; -- tune
 · let u:=stem oX (p.1.val).1; have hp : aZ.1-x=u:= by change prospect x (p.1.val).1-x=u; change x+u-x=u; abel
   unfold boilG; rw [hp]; let P:=p.1.val.2
   let Y:= E_D i.1; have ht:faceT (loomH Y (dye i.2)) P.val.1 P.val.2 u= (faceT Y P.val.1 P.val.2 u) • dye i.2:=by
      unfold faceT; rw [sum_smul]; exact sum_congr rfl fun k _=> (mul_smul ..).symm
   rw [ht]; rfl -- tune
 · have ht:=sam_K n x p; change _< n.val*2; omega
 change 10≤ n.val*2; omega
end YM.GaugeFieldConstruction.Wick.Yacht.Vesper
end
