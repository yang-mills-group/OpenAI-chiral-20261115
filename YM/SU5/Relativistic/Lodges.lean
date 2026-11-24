import YM.SU5.Relativistic.Sangre
import YM.Work.F03.Flat
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Papyrus.Mosaic
open Function Finset Filter MeasureTheory Lattice Wilson Fixed.Pivots Precision RG Work.F03
open Next.SectorChange
open scoped Matrix BigOperators Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable (G : Gauge){W : Side}
local notation "X"=> Config G W
local notation "H"=> Face (Per W)
local notation "ι"=> livelies W
local notation "F"=> Lo W
local notation "Y"=> F→ G.El
open MinorPins GaugeFlux Pharos Exterior
open YM.Push
local notation "K"=> (Fresco G W→ ℝ)
-- identity geometry and grouped linear read
lemma tile_roll (v:ℝ)(u:K) : layOut G (release (1:Y) (tape (v • u)))=represent (v • brightQ G W u):=by
 funext i; unfold layOut; rw [represent_link]; let e:= crosses G W; let F':=smear e *ᵥ u; let x:= brightQ G W u
 have ht(i:Link W) (j:G.ColorIndex): x (i.1,coord i.2) j= F' (i,j):= congrArg (fun t:G.Color=> t j) (craft_t G _ _)
 split
 · next g=>
    change G.lieExp _*1= G.lieExp (v • x _); rw [mul_one]; congr 1; ext j; rw [tape_ap,PiLp.smul_apply,ht]; exact (congrArg (fun r:ℝ=> v • r) (smear_t (e:=e) u (⟨i,g⟩,j)).symm)
 next g=> change _= G.lieExp (v • x _); rw [show x (i.1,coord i.2)=0 from ?_,smul_zero,G.mat_lieExp_zero]; ext j; rw [ht]; exact smear_f _ _ (by rintro ⟨p,h⟩; exact g ((show p.1.val=i from congrArg Prod.fst h) ▸ p.1.property)) -- tune names
open AnalyticBridge.SectorAffine
variable (p:Clip) {σ C Λ:ℝ} (D:ℕ)
open scoped Classical
lemma order_t {V:PathData G} (x:fieldDir G W 1) (u:H) (B:V.Bounds p σ C Λ): cropL G V D x u=∑ i∈Stack.allShort D, Stack.grouped V u.2 i • faceCurl (slotFace i u.1) x:=by
 let f(i:Slot):= faceCurl (slotFace i u.1) x
 have he(i:Slot): HasSum (fun j=>Stack.subCost V u.2 i j • f i) (Stack.grouped V u.2 i • f i):= (Stack.sums B u.2 i).hasSum.smul_const _
 have ht: HasSum (fun j=> ∑ i∈Stack.allShort D, Stack.subCost V u.2 i j • f i) _:=hasSum_sum (s:=Stack.allShort D) fun j _=>he j
 refine Eq.trans ?_ ht.tsum_eq; apply tsum_congr; intro i; split
 · next h=>
    let z:= (V.row u.2 i).2; rw [sum_eq_single_of_mem z ((Stack.short_iff ..).mpr h)]; · unfold Stack.subCost; rw [if_pos (show _ = z from rfl)]; -- defeq
    intro j hj t; unfold Stack.subCost; rw [if_neg (show _ ≠ j from Ne.symm t),zero_smul] -- tune
 next h=>
    refine (sum_eq_zero fun j w=>?_).symm; have hv: (V.row u.2 i).2 ≠ j:=fun g=> h ((Stack.short_iff ..).mp (g.symm ▸ w)); rw [Stack.subCost,if_neg hv,zero_smul] -- tune

-- laws chamber at moving clock. Show exponent *difference*, even moving arrays.
variable (U:ℕ→PathData G)(x:ℕ→ℝ)(B:∀ i,(U i).Bounds p σ C Λ)(hx:Tendsto x atTop (𝓝[≠] 0))
include hx B
lemma on_wire (v:K)(a: H) : let V:=brightQ G W v; let z(i:ℕ):= cropL G (U i) D V a; let Z(i:ℕ):=(x i)⁻¹ • Pressure.shorten (U i) D 1 (represent ((x i) • V)) a; Tendsto (fun i=> ‖Z i-z i‖) atTop (𝓝 0) ∧ ∃ q:ℝ,∀ i,‖z i‖≤q:=by
 intro V z Z; let P:= Stack.allShort D; let A(i:ℕ)(w:Slot):= Stack.grouped (U i) a.2 w; let q:= ∑ i∈ P,C*‖faceCurl (slotFace i a.1) V‖
 have he(i:ℕ) : z i= ∑ w∈P,A i w • faceCurl (slotFace w a.1) V:= order_t G p D V a (B i)
 have ht(i:ℕ)(w:Slot)(t:w∈P): |A i w|≤ C:=le_trans (single_le_sum (f:=fun w=>|A i w|) (fun _ _=>abs_nonneg _) t) (BProof.Charge.grouped_cost p (U i) D (B i) _)
 constructor; swap
 · refine ⟨q,fun i=>?_⟩; rw [he]; exact (norm_sum_le ..).trans (sum_le_sum fun j h=>by rw [norm_smul]; exact mul_le_mul_of_nonneg_right (ht i j h) (norm_nonneg _))
 let Fer(i:ℕ)(w: Slot):= (x i)⁻¹ • w.atSite (represent ((x i) • V)) a.1 - faceCurl (slotFace w a.1) V
 have hv(w:Slot):Tendsto (fun i=> C*‖Fer i w‖) atTop (𝓝 0):=by
    have hp:=(((slot_limit w a.1 V).comp hx).sub_const (faceCurl (slotFace w a.1) V)).norm; simpa only [sub_self,norm_zero,mul_zero,Fer,comp_apply] using! hp.const_mul C
 have hq:= tendsto_finsetSum (s:=P) (f:=fun j i=> C*‖Fer i j‖) (fun j _=> hv j) -- names
 rw [sum_const_zero] at hq; refine squeeze_zero (fun _=>norm_nonneg _) (fun i=>?_) hq
 rw [he,show Z i=∑ j∈P, A i j • ((x i)⁻¹ • (j.atSite (represent (x i • V)) a.1)) from ?_, ← sum_sub_distrib]; swap
 · unfold Z; rw [BProof.Charge.shorten_data p (U i) D _ (B i),smul_sum]; exact sum_congr rfl fun _ _=>smul_comm ..
 exact (norm_sum_le ..).trans (sum_le_sum fun j t=>by rw [← smul_sub,norm_smul]; exact mul_le_mul_of_nonneg_right (ht i j t) (norm_nonneg _))

omit hx B in
private theorem nearSq {G:Type}[NormedAddCommGroup G](a b:ℕ→G)(h:Tendsto (fun i=> ‖a i-b i‖) atTop (𝓝 0))(g:∃ q:ℝ,∀ i, ‖b i‖≤q): Tendsto (fun i=> ‖a i‖^2-‖b i‖^2) atTop (𝓝 0):=by
 obtain ⟨q,s⟩:=g
 let f(i:ℕ):= ‖a i-b i‖; let K':= fun i=> f i*(f i+2*q)
 have ht(i:ℕ):|‖a i‖^2-‖b i‖^2|≤ K' i :=by
    rw [show ‖a i‖^2-‖b i‖^2=(‖a i‖-‖b i‖)*(‖a i‖+‖b i‖) by ring,abs_mul,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]; have hp:=s i; refine mul_le_mul (abs_norm_sub_norm_le ..) ?_ (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _); have hh:= norm_sub_norm_le (a i) (b i); unfold f; linarith
 have hh : Tendsto K' atTop (𝓝 0):=by simpa using h.mul (h.add_const (2*q))
 refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ hh (fun i=>(abs_le.mp (ht i)).1) (fun i=>(abs_le.mp (ht i)).2); simpa using hh.neg
lemma slips (v:K): let z:=brightQ G W v; Tendsto (fun i=> ((x i)⁻¹)^2 * boxE G (U i) D p (represent (x i • z)) - dotProduct v (DueQ G (U i) D (B i) W *ᵥ v)) atTop (𝓝 0):=by
 intro z; let Fer (i:ℕ):= represent (x i • z); let Z (i:ℕ)(b:H):=(x i)⁻¹ • Pressure.shorten (U i) D 1 (Fer i) b; let Y' (i:ℕ)(b:H):=cropL G (U i) D z b
 have hp(b:H): Tendsto (fun i=>‖Z i b‖^2-‖Y' i b‖^2) atTop (𝓝 0):= (nearSq (fun i=> Z i b) _ (on_wire G p D U x B hx v b|>.1) (on_wire G p D U x B hx v b|>.2)) -- omit variable auto
 have he(b:H): Tendsto (fun i=> p.direct*((x i)⁻¹^2*girth G (Fer i) b^2-‖faceCurl b z‖^2)) atTop (𝓝 0):=by
    have hl: faceValue (represent ((0:ℝ) • z)) b=1:=by rw [zero_smul]; exact stroll_zero ..
    have hm: Tendsto (fun i=> G.price (faceValue (Fer i) b)/ x i^2) atTop (𝓝 (‖faceCurl b z‖^2/2)):= (price_limit hl (face_deriv b z)).comp hx
    have hz : Tendsto (fun i=> (x i)⁻¹^2*girth G (Fer i) b^2) atTop (𝓝 (‖faceCurl b z‖^2)):=by
       have ht:=hm.const_mul 2; convert! ht using 2 <;> first| rfl| (simp only [girth,G.chord_price,div_eq_mul_inv,inv_pow]; ring)| ring
    exact (show p.direct*(‖faceCurl b z‖^2-‖faceCurl b z‖^2)=0 by rw [sub_self,mul_zero]) ▸ (hz.sub_const (‖faceCurl b z‖^2)).const_mul p.direct -- tune
 let P:= plumb W D; let A:=ort W
 have ht:= (tendsto_finsetSum P (fun b _=> hp b)); have hh:=tendsto_finsetSum A (fun b _=> he b)
 rw [sum_const_zero] at ht hh; have hy:= hh.add ht; rw [add_zero] at hy; apply hy.congr' (Eventually.of_forall _); intro i; rw [show dotProduct v _= _ from ledgerQ G (U i) D (B i) v]; unfold boxE shortV crateB inCurl; simp_rw [Z,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,mul_sub,sum_sub_distrib,←Finset.mul_sum]; unfold P A Fer Y'; unfold z; ring -- tune
end YM.CF.Papyrus.Mosaic
#print axioms YM.CF.Papyrus.Mosaic.slips
