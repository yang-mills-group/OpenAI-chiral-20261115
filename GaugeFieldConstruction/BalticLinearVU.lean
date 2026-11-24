import GaugeFieldConstruction.MingRecsVU
/-! Linear combinations too: no test in this pencil annihilates against the elected prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Invoice.curvΝ
open YM.Boundary
open MeasureTheory Set Filter Function Mink Spectral Complex Finset
open scoped Topology BigOperators InnerProductSpace Matrix Classical
variable {A: Type} [Ring A] [Algebra ℂ A]
def Constr4VU (X:A→ₗ[ℂ]ℂ) : A→ₗ[ℂ] A→ₗ[ℂ]ℂ where
 toFun x:= { toFun:= fun y=> X (x*y)- X x*X y
             map_add':= fun y z=>by rw [mul_add,map_add,map_add,mul_add]; ring
             map_smul':= fun c y=> by rw [mul_smul_comm,map_smul,map_smul]; change _= c • _; simp only [smul_eq_mul]; ring }
 map_add' x y:= by ext v; change X ((x+y)*v)-X _* X _=_+ (X _-X _*X _); rw[add_mul,map_add,map_add,add_mul]; simp only [LinearMap.coe_mk,AddHom.coe_mk]; ring
 map_smul' c y:=by ext z; change X ((c • y)*z)-X _*X z= c • (X _-X _*X z); rw [smul_mul_assoc,map_smul,map_smul]; simp only [smul_eq_mul]; ring
abbrev SelectLoomVU (F:ClanZN→A)(v:SΝΨ):= ∑ i:ClanZN, starRingEnd ℂ (v i) • F i
abbrev SelectCastVU (F:ClanZN→A)(v:SΝΨ):= ∑ i:ClanZN, v i • F i
variable (X:A→ₗ[ℂ]ℂ)(F G:ClanZN→A)
lemma FormsPriceVU (v:SΝΨ): Constr4VU X (SelectLoomVU F v) (SelectCastVU G v)= Formsν (fun i j=>Constr4VU X (F i) (G j)) v:=by
 unfold SelectLoomVU; rw [map_sum (Constr4VU X),LinearMap.sum_apply]; unfold Formsν; refine sum_congr rfl (fun i _=>?_); rw [map_smul (Constr4VU X),LinearMap.smul_apply]; unfold SelectCastVU; rw [map_sum, Finset.smul_sum]; exact sum_congr rfl (fun j _=> by rw [map_smul]; simp only [smul_eq_mul]; rw [mul_assoc]) -- tune mul_sums
lemma TruePricesVU (v:SΝΨ)(h:v≠0){r:ℝ}(p:0<r)(e:(fun i j:ClanZN=>Constr4VU X (F i) (G j))∈PrecisionYN r): Constr4VU X (SelectLoomVU F v) (SelectCastVU G v)≠0:=by
 let c:ℂ:= (↑‖v‖:ℂ)⁻¹; rw[FormsPriceVU]; intro u
 have ht:r<(Formsν _ (c • v)).re:= e _ (normShipsVU v h); rw[HankMeasureVU v c,u,mul_zero,zero_re] at ht; linarith
#print axioms Constr4VU
#print axioms TruePricesVU
end YM.GaugeFieldConstruction.Invoice.curvΝ
