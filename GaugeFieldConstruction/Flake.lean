import GaugeFieldConstruction.AngularF

/-!
# Coordinates in the X summand: no kernel in these axes when sorted.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 5000
noncomputable section
namespace YM.GaugeFieldConstruction.Stage.Count
open Calibration Calibration.RawBank Floor Raw Phys Cauchy Row Record Function Filter Set Complex Wide Stage.Cell
open scoped BigOperators Topology
abbrev XX := UX five
abbrev BH := (mixed five).moves

def source (i : X5): XX:= (DeckX five).issue (ket ((i.1,i.2.toBlade.val) : BoxX five))
lemma source_eq (i : X5): (source i).val=evalX i:= (DeckX five).paid_at _
local instance aux : AddCommGroup XX := @Submodule.addCommGroup ℂ (J Row.x) _ _ _ _
lemma paid_sources : Surjective (jet source) := by
  refine LinearMap.range_eq_top.mp (top_unique fun i _=> ?_)
  obtain ⟨u,pu⟩:=i.property -- span U? use
  let p (k : X5):=ket k
  refine ⟨(∑ i:X5, u i • p i),?_⟩
  apply Subtype.ext; rw [← pu]; change _=∑ i:X5,u i • evalX i
  rw [map_sum]; simp only [map_smul];
  rw [show ∀ (f : X5→XX), (∑ i,f i).val=∑ i,(f i).val from fun f=>map_sum (SX five).subtype f Finset.univ]
  exact Finset.sum_congr rfl fun i _ => by dsimp only [p]; rw [on_ket, Submodule.coe_smul_of_tower,source_eq]

-- λ probes dual on both structures. g dual via existence by finite scans pair (test φ,ψ dot spatial basis). easiest `Bill` certify all evalX linearIndependent. or prove Leg `F i j` distinct. use F_x basis Gram of ordered first derivatives. finite evidence projection inner with `test *` encode Money. construct dual column F via element coordinates and star, pair Binner=2, Finner=1. finite check arc arrays by decide list verify. alternatives finite tactic `fin_cases` Wed (nondecodable?)

private def probeB (i : Axis) : J f→ₗ[ℂ] ℂ := ∑ a: Cauchy.Spin,∑ b:Cauchy.Spin, (star (Hij i a b) / 2 : ℂ) • (Finsupp.lapply ((a,(0:MI)),(b,(0:MI))))
private lemma probeK (i j : Axis): probeB i (Row.B j)=(if i=j then 1 else 0) := by
  have ht (i j) a b : (∑ c:Cauchy.Spin,∑ k:Cauchy.Spin,(star (Hij i c k)/2:ℂ) • (Finsupp.lapply (R:=ℂ) ((c,(0:MI)),(k,(0:MI))))) (Hij j a b • times' (C a 0) (C b 0))= Hij j a b*(star (Hij i a b)/2) := by
    unfold C; rw [takes]; simp_rw [LinearMap.sum_apply,LinearMap.smul_apply,map_smul]
    fin_cases a <;> fin_cases b <;> simp [ket,mul_comm]
  unfold Row.B; rw [map_sum]; simp_rw [map_sum]; unfold probeB; simp_rw [ht]
  fin_cases i <;> fin_cases j <;> norm_num [Hij] <;> first| done| (ring_nf <;> simp)
private def probeF (v : Wed):GJet →ₗ[ℂ] ℂ := jet (fun i=>star ((Row.arc v) i))
private lemma probeJ (i j : Wed) : probeF i (Row.arc j)=if i=j then 1 else 0 := by
  let f(w : Vouchers.Bill GIndex) (r:Vouchers.Bill GIndex):Vouchers.Credit:= Vouchers.Credit.sum (w.map fun p=> p.2 * (Vouchers.Credit.silver (Vouchers.Bill.cash p.1 r)))
  let v:= Vouchers.Camera.pixel
  have he : ∀ (a b : Wed), f (v b) (v a)=if a=b then 1 else 0 := by dsimp only [f,v]; decide +kernel
  have ht (r : Vouchers.Bill GIndex): (f r (v i)).money = probeF i (Vouchers.Bill.total r) := by
    induction r with
    | nil=> simp [f, Vouchers.Credit.sum,Vouchers.Bill.total]
    | cons x q h=>rw [show f (x::q) (v i)=x.2*Vouchers.Credit.silver (Vouchers.Bill.cash x.1 (v i))+ f q (v i) from rfl,Vouchers.Credit.plus,h, Vouchers.Credit.times, Vouchers.Credit.cc, Vouchers.Bill.spendable,show Vouchers.Bill.total (v i) = Row.arc i from Vouchers.Camera.pixel_cost i,Vouchers.Bill.total,map_add,map_smul,probeF,on_ket]; rfl
  rw [← Vouchers.Camera.pixel_cost,← show (f (v j) (v i)).money=_ from ht (v j),he]; split_ifs <;> simp

def external (i : X5) : XX→ₗ[ℂ] ℂ:= productRead (probeB i.1) (probeF i.2) ∘ₗ (SX five).subtype
lemma window (i j:X5) : external i (source j)= if i=j then 1 else 0 := by
  rcases i with ⟨a,b⟩; rcases j with ⟨x,y⟩; unfold external; rw [LinearMap.comp_apply,Submodule.subtype_apply,source_eq,evalX,read_times, probeK,probeJ]; dsimp only; split_ifs <;> simp_all
lemma issue (x:J X5) (i:X5) : external i (jet source x)=x i := by
  suffices H: (external i) ∘ₗ jet source=Finsupp.lapply i from LinearMap.congr_fun H x
  apply ket_ext; intro j; rw [LinearMap.comp_apply,on_ket,window]; simp [ket,eq_comm,Finsupp.single_apply]
lemma paid_ext (q : XX) (p:∀ i,external i q=0): q=0 := by
  obtain ⟨x,rfl⟩:=paid_sources q; simp_rw [issue] at p
  rw [show x=0 from Finsupp.ext p,map_zero]

lemma beam (s t): BH s (source t)=pay (x5Act.cost s t) (source (x5Act.move s t)) := by
  apply Subtype.ext; apply ext_jet recX.faith; intro w; obtain ⟨u,p⟩:= recX.permit s w
  rw [← (mixed five).transit p,source_eq,readingX.moving s w u p]; cases he:x5Act.cost s t <;> simp only [pay_false,pay_true,Submodule.coe_neg,source_eq,map_neg]
end YM.GaugeFieldConstruction.Stage.Count
