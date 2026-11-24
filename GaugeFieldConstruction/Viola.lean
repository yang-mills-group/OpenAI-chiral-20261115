import GaugeFieldConstruction.Vaults
/-
The actual spatial-jet indices hit the full real Gem and the first Maxwell-Live slot.
Proof avoids Fourier positivity on a tight time aperture.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 40000
noncomputable section
namespace YM.GaugeFieldConstruction.Wick.Yacht.Vesper
open StressFHeat MeasureTheory Analysis Function Filter Metric Maxwell Finset Gap Complex Cauchy Row Phys Flux.One Lamp Conj
open Lattice CF CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart CF.Py.Rate.LocalLimit.Papal
open scoped Topology ContDiff BigOperators InnerProductSpace Classical
open HopeC CF.Buffered CF.Buffered.Lifted FlightFlux Fluxim TableF TableF.Lenten Layout Shield Wilson Raw
open U1 Gauge97
open Record
local instance : AddCommGroup ↥G3:= PackG.G.toAddCommGroup
local instance : Module ℂ ↥G3:= PackG.S.toModule
-- anchors before P allocation. general builders. η.Res.comp
variable {A B: Type} [NormedAddCommGroup A] [NormedSpace ℝ A][FiniteDimensional ℝ A][NormedAddCommGroup B][NormedSpace ℝ B][FiniteDimensional ℝ B]
/-- ℝ-bilinear corner at a wedge-derivative pair. -/
def kite (f:A→ₗ[ℝ]ℝ)(g:B→ₗ[ℝ]ℝ):leadF A B:=f.toContinuousLinearMap.smulRight (ofRealCLM.comp g.toContinuousLinearMap)
lemma kite_h(f:A→ₗ[ℝ]ℝ)(g:B→ₗ[ℝ]ℝ)(a b):kite f g a b=(f a:ℂ)*(g b:ℂ):= rfl -- spin? smul real complex not rfl
variable {α β: Type}[Fintype α][Fintype β][DecidableEq α][DecidableEq β]
-- q inject → resolution
private lemma Tariff (f:α→ A→ₗ[ℝ]ℝ)(e:∀ X:A,(∀ i,f i X=0)→X=0):∃ c:α→ A,∀ X:A,∑ i,f i X • c i=X:=by
 let T:= LinearMap.pi f; have hp: LinearMap.ker T=⊥:= le_antisymm (fun x p=>e _ fun i=>congrFun (show T x=0 from p) i) bot_le
 obtain ⟨P,h⟩:= LinearMap.exists_leftInverse_of_injective T hp
 refine ⟨fun i=>P (Pi.single i 1),fun X=>?_⟩; simp_rw [← map_smul P]; rw [←map_sum]; rw [show ∑ i,(f i X) • Pi.single i (1:ℝ)=T X from (by ext1 i; rw [Finset.sum_apply]; simp [T,Pi.single_apply])]; exact LinearMap.congr_fun h X
lemma revival (f:α→ A→ₗ[ℝ]ℝ)(e:∀ a,(∀ i,f i a=0)→a=0)(g:β→ B→ₗ[ℝ]ℝ)(u:∀ a,(∀ i,g i a=0)→a=0)
 (h:leadF A B): ∃ c:α→β→ℂ,h=∑ i,∑ j,c i j • kite (f i) (g j):=by
 obtain ⟨p,P⟩:=Tariff f e; obtain ⟨q,Q⟩:=Tariff g u; refine ⟨fun i j=> h (p i) (q j),?_⟩; apply ContinuousLinearMap.ext; intro a; apply ContinuousLinearMap.ext; intro b; conv_lhs=> rw [← P a,← Q b]
 rw [map_sum h]; simp_rw [ContinuousLinearMap.sum_apply]
 apply sum_congr rfl; intro i _; rw [map_sum]; apply sum_congr rfl; intro j _; rw [map_smul,map_smul,ContinuousLinearMap.smul_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.smul_apply,kite_h]; simp only [real_smul,smul_eq_mul]; ring -- tune
-- Gauge modules
abbrev PairD:=Axis×Wed
def blueL (W:Wed): Gem→ₗ[ℝ]ℝ where
 toFun i:=i.val W.toBlade.val.1 W.toBlade.val.2
 map_add' _ _:=rfl
 map_smul' _ _:=rfl
def blueP (p:PairD):Sut→ₗ[ℝ]ℝ where
 toFun i:=i.val p.1 p.2.toBlade.val.1 p.2.toBlade.val.2
 map_add' _ _:=rfl
 map_smul' _ _:=rfl
lemma blue_s(i:Gem)(h:∀ j, blueL j i=0):i=0:=by
 apply Subtype.ext; funext j k; change i.val j k=0; rcases lt_trichotomy j k with p|rfl|p; exact h (Wed.mk j k p); exact fluxZ ..; exact (flux_neg i j k).trans ((congrArg Neg.neg (h (Wed.mk k j p))).trans neg_zero)
lemma blue_C(i:Sut)(h:∀ j, blueP j i=0): i=0:=by
 apply Subtype.ext; funext t j k; change i.val t j k=0; rcases lt_trichotomy j k with p|rfl|p; exact h (t, Wed.mk j k p); exact F_slot0 ..; exact (F_neg i t j k).trans ((congrArg Neg.neg (h (t,Wed.mk k j p))).trans neg_zero)
def k3(i j:Wed): G3:=by
 let p:=kite (blueL i) (blueL j); exact ⟨p+p.flip, by change (p+p.flip).flip=p+p.flip; apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j; exact add_comm ..⟩ -- tune
abbrev k5(i:Wed)(j:PairD): Gκ:=kite (blueL i) (blueP j)
lemma landsC (i j:Wed)(a b:Gem): (k3 i j).val a b=kite (blueL i) (blueL j) a b+kite (blueL i) (blueL j) b a:=rfl
lemma basinG (p:G3):∃ c: Wed→Wed→ℂ, p=∑ i,∑ j,c i j • k3 i j:=by
 obtain ⟨c,h⟩:=revival blueL blue_s blueL blue_s p.val; refine ⟨fun i j=>(1/2:ℂ)*c i j,?_⟩
 have hv: p.val.flip=p.val:=p.property
 apply Subtype.ext; apply ContinuousLinearMap.ext; intro x; apply ContinuousLinearMap.ext; intro y
 let K(i j:Wed):=kite (blueL i) (blueL j)
 have he:p.val x y=(1/2:ℂ)*(p.val x y)+(1/2:ℂ)*(p.val y x):=by
    rw [show p.val y x=p.val x y from DFunLike.congr_fun (DFunLike.congr_fun hv x) y]; ring
 rw [he,h]; simp_rw [Submodule.coe_sum, Submodule.coe_smul, ContinuousLinearMap.sum_apply,Finset.mul_sum,← Finset.sum_add_distrib]; exact sum_congr rfl fun i _=> sum_congr rfl fun j _=> by rw [ContinuousLinearMap.smul_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,ContinuousLinearMap.smul_apply,landsC]; change ((1/2:ℂ)*(c i j*K i j x y)+(1/2:ℂ)*(c i j*K i j y x))= ((1/2:ℂ)*c i j)*(K i j x y+K i j y x); ring -- tune
lemma basinD(p:Gκ):∃ c:Wed→PairD→ℂ,p=∑ i,∑ j,c i j • k5 i j:=revival blueL blue_s blueP blue_C p
-- Can use $Λ$ as chosen Gingrik.S
lemma tallG(p:G3) : ∃ q:J Row.g, q∈ gFour∧∀ i j:GIndex,test (i,j) q=p.val (E_G i) (E_G j):=by
 obtain ⟨c,h⟩:=basinG p; let K(i j:Wed):= Bose (arc i) (arc j); refine ⟨∑ i,∑ j,c i j • K i j,Submodule.sum_mem _ (fun i _=>Submodule.sum_mem _ (fun j _=>gFour.smul_mem _ ?_)),?_⟩
 · unfold gFour Record.space; rw [Fintype.range_linearCombination]; refine Submodule.subset_span ⟨ordered i j,?_⟩; unfold ordered; split; exact bose_swap ..; rfl
 intro i j; rw [h]; simp_rw [Submodule.coe_sum,map_sum,ContinuousLinearMap.sum_apply]; apply sum_congr rfl; intro a _; apply sum_congr rfl; intro b _; rw [map_smul,Submodule.coe_smul,ContinuousLinearMap.smul_apply,ContinuousLinearMap.smul_apply]; unfold K; rw [Bose,map_add,tested,tested,landsC,kite_h,kite_h]; congr 1; have hx(i:GIndex)(j: Wed):test i (arc j)= ↑(blueL j (E_G i)):=portal ..
 simp_rw [hx]; congr 1; ring -- tune
lemma tallD(p:Gκ):∃ q: J Row.g,q∈space evalG∧∀ i j:GIndex,test (i,j) q=p (E_G i) (E_D j)+p (E_G j) (E_D i):=by
 obtain ⟨c,h⟩:=basinD p; let X(i:Wed)(j:PairD):=evalG (i,j.2,j.1)
 refine ⟨∑ i,∑ j,c i j • X i j,Submodule.sum_mem _ (fun i _=>Submodule.sum_mem _ (fun j _=>(space evalG).smul_mem _ ?_)),?_⟩
 · unfold space; rw [Fintype.range_linearCombination]; exact Submodule.subset_span ⟨_,rfl⟩ -- tune metav
 intro i j; rw [h]; simp_rw [map_sum,ContinuousLinearMap.sum_apply,←sum_add_distrib]; apply sum_congr rfl; intro a _; apply sum_congr rfl; intro b _; let D:=Gder b.1 (arc b.2); change test _ (c a b • Bose (arc a) D)= (c a b • k5 a b (E_G i) (E_D j))+(c a b • k5 a b (E_G j) (E_D i)); rw [map_smul,Bose,map_add,tested,tested,← smul_add]; unfold k5; rw [kite_h,kite_h]; congr 1; have hx(i:GIndex): test i (arc a)=↑(blueL a (E_G i)):=portal ..; have hv(i:GIndex):test i D=↑(blueP b (E_D i)):=portion ..; rw [hx,hx,hv,hv,mul_comm (↑(blueP b _):ℂ)] -- tune mul reorder
end YM.GaugeFieldConstruction.Wick.Yacht.Vesper
end
