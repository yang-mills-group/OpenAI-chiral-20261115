import GaugeFieldConstruction.Viola
import GaugeFieldConstruction.Pleiad
/-
The actual spatial-jet indices hit the full real Gem and the first Maxwell-Live slot.
Proof avoids Fourier positivity on a tight time aperture.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 155000
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
-- Claim R1 schema. map and ker. CF.Path not Shelf.
def μG : ↥G3 →ₗ[ℂ] J Row.g where
 toFun a:= (tallG a).choose
 map_add' x y:=Finsupp.ext fun ⟨i,j⟩=> ((tallG (x+y)).choose_spec.2 i j).trans <|congrArg₂ (·+·) ((tallG x).choose_spec.2 i j).symm ((tallG y).choose_spec.2 i j).symm
 map_smul' r a:=Finsupp.ext fun ⟨i,j⟩=> ((tallG (r • a)).choose_spec.2 i j).trans <|congrArg (fun x:ℂ=> r • x) ((tallG a).choose_spec.2 i j).symm
def μD:Gκ→ₗ[ℂ] J Row.g where
 toFun a:= (tallD a).choose
 map_add' x y:=by
    apply Finsupp.ext; rintro ⟨i,j⟩; change test (i,j) (tallD (x+y)).choose= test (i,j) ((tallD x).choose+(tallD y).choose); rw [map_add]; rw [show test (i,j) _=_ from (tallD (x+y)).choose_spec.2 i j] -- coercion
    rw [show test (i,j) _=_ from (tallD x).choose_spec.2 i j,show test (i,j) _=_ from (tallD y).choose_spec.2 i j]; simp only [_root_.add_apply]; abel
 map_smul' r a:=by
    apply Finsupp.ext; rintro ⟨i,j⟩; change test (i,j) (tallD (r • a)).choose= test (i,j) (r • (tallD a).choose); rw [map_smul]; rw [show test (i,j) _=_ from (tallD (r • a)).choose_spec.2 i j,show test (i,j) _=_ from (tallD a).choose_spec.2 i j]; simp only [_root_.smul_apply, RingHom.id_apply,smul_add]
lemma milkG(p:G3): μG p∈gFour∧∀ i j:GIndex,test (i,j) (μG p)= p.val (E_G i) (E_G j):=(tallG p).choose_spec
lemma milkD(p:Gκ): μD p∈ space evalG∧∀ i j:GIndex,test (i,j) (μD p)=p (E_G i) (E_D j)+ p (E_G j) (E_D i):=(tallD p).choose_spec
lemma boltP (a b: Wed): μG (k3 a b) = Bose (arc a) (arc b):=by
 ext1 ⟨x,y⟩; change test (x,y) (μG (k3 a b))= test (x,y) (Bose (arc a) (arc b)); rw [(milkG _).2,landsC,Bose,map_add,tested,tested,kite_h,kite_h]; have hp(i j):test i (arc j)= ↑(blueL j (E_G i)):= portal ..; simp_rw [hp]; congr 1; ring
lemma boltW(a:Wed)(b:PairD):μD (k5 a b)= Bose (arc a) (Gder b.1 (arc b.2)):=by
 ext1 ⟨x,y⟩; change test (x,y) (μD (k5 a b))= test (x,y) (Bose (arc a) (Gder b.1 (arc b.2))); rw [(milkD _).2,Bose,map_add,tested,tested]; unfold k5; rw [kite_h,kite_h]; have hp(i j):test i (arc j)=↑(blueL j (E_G i)):=portal ..; have hk(i): test i (Gder b.1 (arc b.2))=↑(blueP b (E_D i)):=portion ..; simp_rw [hp,hk]; congr 1; ring
lemma wonG: LinearMap.range μG=gFour:=by
 refine le_antisymm (fun i ⟨p,h⟩=> h ▸ (milkG p).1) ?_; unfold gFour space; rw [Fintype.range_linearCombination]; apply Submodule.span_le.mpr; rintro y ⟨x,rfl⟩; exact ⟨_,boltP x.val.1 x.val.2⟩
lemma wonD:LinearMap.range μD=space evalG:=by
 refine le_antisymm (fun i ⟨p,h⟩=> h ▸ (milkD p).1) ?_; unfold space; rw [Fintype.range_linearCombination]; apply Submodule.span_le.mpr; rintro y ⟨x,rfl⟩; exact ⟨_,boltW x.1 (x.2.2,x.2.1)⟩
lemma kinG (A:G3)(B:Gκ) : μG A+ μD B=0 ↔ A=0∧∀ (i:Gem)(j:Sut), j∈liveD → B i j=0:=by
 refine ⟨fun p=>?_,fun ⟨e,v⟩=>?_⟩
 · have hp(i j:GIndex): A.val (E_G i) (E_G j)+(B (E_G i) (E_D j)+ B (E_G j) (E_D i))=0:=by rw [←(milkD ..).2, ←(milkG ..).2,←map_add,p,map_zero]
   apply And.intro
   · have he(x y:SayL): A.val (E_G (winkL x.1 x.2)) (E_G (winkL y.1 y.2))=0:=by
        have ht:=hp (winkL x.1 x.2) (winkL y.1 y.2); rw [partedE x, partedE y,map_zero,map_zero,add_zero,add_zero] at ht; exact ht
     apply Subtype.ext; apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j; change A.val i j=0; rw [bead_g i, bead_g j, map_sum A.val, ContinuousLinearMap.sum_apply]; apply sum_eq_zero; intro k _; rw [map_sum]; apply sum_eq_zero; intro l _; rw [map_smul,map_smul,ContinuousLinearMap.smul_apply,he k l,smul_zero,smul_zero]
   intro i j e; have he (x:SayL)(y:WaveL):B (E_G (winkL x.1 x.2)) (E_D (wallU y))=0:=by
      have ht:= hp (winkL x.1 x.2) (wallU y); rw [partedD,partedE, map_zero,map_zero,add_zero,zero_add] at ht; exact ht -- maybe no x arg
   conv=>lhs; rw [bead_g i,bead_w j e, map_sum B,ContinuousLinearMap.sum_apply]
   apply sum_eq_zero; intro k _; rw [map_sum]; apply sum_eq_zero; intro l _; rw [map_smul,map_smul, ContinuousLinearMap.smul_apply]; change _ • (beadL i k • B _ (E_D (wallU l)))= _; rw [he k l, smul_zero,smul_zero]
 ext1 ⟨i,j⟩; rw [Finsupp.add_apply,e,map_zero,Finsupp.zero_apply, zero_add]; exact ((milkD B).2 i j).trans (by rw [v _ _ (no_fee _),v _ _ (no_fee _),add_zero]) -- tune
lemma fossil{E F:Type}[AddCommGroup E][Module ℝ E][AddCommGroup F][Module ℝ F] (p:E→ₗ[ℝ]F):∃ q:F→ₗ[ℝ] E,∀ i,p (q (p i))=p i:=by
 let T:=LinearMap.range p; obtain ⟨q,H⟩:= p.rangeRestrict.exists_rightInverse_of_surjective p.range_rangeRestrict; obtain ⟨L,h⟩:= T.subtype.exists_leftInverse_of_injective T.ker_subtype
 refine ⟨q.comp L,fun i=>?_⟩; let x:T:=p.rangeRestrict i; have hv:L (p i)=x:=LinearMap.congr_fun h x; have ht: p (q x)=p i:=congrArg (fun i:LinearMap.range p=> i.val) (LinearMap.congr_fun H x); rw [LinearMap.comp_apply,hv]; exact ht
def blast (x:Axis)(a:Wed):Gκ:= kite (blueL a) ((LinearMap.proj x).comp breezeD)
lemma crags (B:Gκ)(h:∀(i:Gem)(j:Sut), j∈liveD → B i j=0):∃ X: Wed→ Axis→ℂ,B= ∑ i,∑ j,X i j • blast j i:=by
 obtain ⟨L,H⟩:= fossil breezeD; have hp(i:Gem)(j:Sut): B i j=B i (L (breezeD j)):=by rw [← sub_eq_zero,← map_sub]; apply h; change breezeD _ =0; rw [map_sub,H,sub_self]
 let Z:=L.toContinuousLinearMap; let Q:leadF Gem (Axis→ℝ):= (B.flip.comp Z).flip; let F(x:Axis):= (LinearMap.proj (R:=ℝ) x : (Axis→ ℝ) →ₗ[ℝ] ℝ)
 obtain ⟨c,g⟩:=revival blueL blue_s F (fun _ p=> funext p) Q
 refine ⟨c,?_⟩; apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j; rw [hp i j,show B i (L (breezeD j))=Q i (breezeD j) from rfl,g]; simp_rw [ContinuousLinearMap.sum_apply]; apply sum_congr rfl; intro a _; apply sum_congr rfl; intro b _; rfl
-- Witness Mark at basis orientation
-- Matrix typeclass at end
end YM.GaugeFieldConstruction.Wick.Yacht.Vesper
end
