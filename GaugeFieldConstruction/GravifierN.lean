import GaugeFieldConstruction.FlamesΦN
set_option autoImplicit false
set_option synthInstance.maxSize 5000
set_option maxRecDepth 4000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.GaugeFieldConstruction.Invoice
open Window Vouchers Abacus Cauchy Row Phys Calibration Function Wick Raster Gap Finset Mirror Floor Flavor
open MeasureTheory Set Filter
open scoped BigOperators Topology Classical ComplexOrder
-- mirror-positive PH. choose actual generation assignments cycling. real part system strength noncollapse when measurements pose neighborhoods. Basis slots at αΦ frame high.
-- dual evaluations
namespace curvΝ
private def probeB (i : Axis) : J f→ₗ[ℂ] ℂ := ∑ a: Cauchy.Spin,∑ b:Cauchy.Spin, (star (Hij i a b) / 2 : ℂ) • (Finsupp.lapply ((a,(0:MI)),(b,(0:MI))))
private lemma probeK (i j : Axis): probeB i (Row.B j)=(if i=j then 1 else 0) := by
  have ht (i j) a b : (∑ c:Cauchy.Spin,∑ k:Cauchy.Spin,(star (Hij i c k)/2:ℂ) • (Finsupp.lapply (R:=ℂ) ((c,(0:MI)),(k,(0:MI))))) (Hij j a b • times' (C a 0) (C b 0))= Hij j a b*(star (Hij i a b)/2) := by
    unfold C; rw [takes]; simp_rw [LinearMap.sum_apply,LinearMap.smul_apply,map_smul]
    fin_cases a <;> fin_cases b <;> simp [ket,mul_comm]
  unfold Row.B; rw [map_sum]; simp_rw [map_sum]; unfold probeB; simp_rw [ht]
  fin_cases i <;> fin_cases j <;> norm_num [Hij] <;> first| done| (ring_nf <;> simp)
lemma ζτN(i:Axis):Row.B i≠0:=fun g=> by have hp:=probeK i i; rw [g,map_zero,if_pos rfl] at hp; exact zero_ne_one hp
abbrev ClanZN := Matter.Generation × Bool
abbrev transitionΦN (i:ClanZN):Matter.FlavorIndex:=(i.2,i.1,i.1+1)
lemma departN (i:ClanZN):(transitionΦN i).2.1≠ (transitionΦN i).2.2:=by rcases i with ⟨i,g⟩; change i≠i+1; fin_cases i<;> decide
lemma tripledΓN:Function.Injective transitionΦN:= fun i j h=>Prod.ext (congrArg (fun x:Matter.FlavorIndex=>x.2.1) h) (congrArg Prod.fst h)
def CauchyAxisN (i:Axis): UF three:=⟨Row.B i, by change Row.B i∈ Record.space Row.B; unfold Record.space; rw [Fintype.range_linearCombination]; exact Submodule.subset_span (Set.mem_range_self _)⟩
lemma CauchyA_N (i:Axis): CauchyAxisN i ≠ 0:=fun g=>ζτN i (congrArg Subtype.val g)
local instance iϕF (d:Floor) : AddCommGroup (UF d):= @Submodule.addCommGroup ℂ (J Row.f) _ _ _ (SF d)
local instance iϕU (d:Floor) : AddCommGroup (UV d):= inferInstanceAs (AddCommGroup (Prod ℂ _))
set_option synthInstance.maxHeartbeats 80000
def FamilyZN (i:Axis)(k:ClanZN): UV three:=(0,0,Pi.single (transitionΦN k) (CauchyAxisN i),0)
lemma StoryZN(i:Axis)(k:ClanZN)(g:CompassN): flavors three g.val (FamilyZN i k)= Flavor.βChiN g (transitionΦN k) • FamilyZN i k:=by
 let x:= transitionΦN k; let b:=βChiN g x; let h:Fragment (UF three):=Pi.single x (CauchyAxisN i); refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
 · exact (smul_zero b).symm
 · exact (smul_zero b).symm
 swap
 · change hues g.val (0:Fragment (UX three)) = b • 0; rw [map_zero,smul_zero]
 change hues g.val h=b • h; ext1 j; rw [Pi.smul_apply]; have he:=plate h g.val j; rw [Flavor.chaseN g j] at he; rw [he]; by_cases v:j=x
 · subst j; change pay (βbitN g x) _=pay (βbitN g x) (1:ℂ) • _; cases βbitN g x <;> simp
 rw [show h j=0 from Pi.single_eq_of_ne v _,pay_zero,smul_zero]
variable (i:Axis)
local notation "J_τ"=> UV three
abbrev RafN (d:Floor)(x:UV d):UV d:= shade d (spinFrame d mirror x)
lemma StoryMZN(k:ClanZN)(g:CompassN): flavors three g.val (RafN three (FamilyZN i k))= Flavor.βChiN g (transitionΦN k) • (RafN three (FamilyZN i k)):=by
 let q:=Flavor.βChiN g (transitionΦN k)
 unfold RafN; rw [←color_s,← (show spinFrame _ _ (flavors _ g.val (FamilyZN i k))= flavors three g.val (spinFrame three mirror (FamilyZN i k)) from LinearMap.congr_fun (Calibration.commute mirror three g.val) _),StoryZN,map_smul,map_smulₛₗ]
 congr 1; unfold βChiN; cases Flavor.βbitN g (transitionΦN k) <;> simp
-- injectivity for matrix proof
lemma AnchorN(k:ClanZN):FamilyZN i k≠0:=fun g=> by
 have he:= congrArg (fun x:J_τ=>x.2.2.1 (transitionΦN k)) g; change (Pi.single (transitionΦN k) _ (transitionΦN k))=0 at he; rw [Pi.single_eq_same] at he; exact CauchyA_N i he
lemma sumN_low (k:ClanZN)(v: ClanZN→ℂ): (∑ j,v j • FamilyZN i j).2.2.1 (transitionΦN k)= v k • CauchyAxisN i:=by
 let u: J_τ→ₗ[ℂ] UF three:=LinearMap.proj (transitionΦN k) ∘ₗ LinearMap.fst .. ∘ₗ LinearMap.snd .. ∘ₗ LinearMap.snd ..
 change u (∑ j,v j • FamilyZN i j) = _; rw [map_sum,sum_eq_single k]; rw [map_smul,show u (FamilyZN i k)=CauchyAxisN i from Pi.single_eq_same ..]
 intro b _ s; rw [map_smul, show u (FamilyZN i b)=0 from Pi.single_eq_of_ne (show transitionΦN k≠transitionΦN b from fun v=>s (tripledΓN v.symm)) _,smul_zero]
 simp
lemma poured_s (a:ClanZN→ℂ)(p:a≠0):∑ j,a j • FamilyZN i j≠0:=by
 intro h; apply p; funext j; have hv:=sumN_low i j a; rw [h] at hv; exact (smul_eq_zero.mp hv.symm).resolve_right (CauchyA_N i)
abbrev Formsν (K:ClanZN→ClanZN→ℂ)(v:ClanZN→ℂ):ℂ:=∑ i:ClanZN,∑ j:ClanZN, starRingEnd ℂ (v i)*v j*K i j
abbrev MatrixWΦN(i:Axis)(j k:ClanZN):ℂ:= stare (couples (shells three (RafN three (FamilyZN i j))) (shells three (FamilyZN i k)))
lemma magnetΓN (v:ClanZN→ℂ)(g:v≠0): 0 < (Formsν (MatrixWΦN i) v).re :=by
 have he:=mirror_positive three (∑ j,v j • FamilyZN i j) (poured_s i v g)
 apply lt_of_lt_of_eq he; apply congrArg Complex.re; simp only [map_sum, LinearMap.sum_apply,map_smul,map_smulₛₗ,LinearMap.smul_apply]; simp_rw [Finset.smul_sum]; rw [_root_.Finset.sum_comm]; unfold Formsν; refine Finset.sum_congr rfl fun a _=> Finset.sum_congr rfl fun b _=>?_; change v b*(starRingEnd ℂ (v a)*_) = _ * MatrixWΦN i a b; exact mul_left_comm .. |>.trans (mul_assoc ..).symm -- tune
end curvΝ
end YM.GaugeFieldConstruction.Invoice
end
