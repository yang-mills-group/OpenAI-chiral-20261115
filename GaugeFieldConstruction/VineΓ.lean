import GaugeFieldConstruction.TrickΛ
set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
namespace YM.GaugeFieldConstruction.Wick.Yacht
open StressFHeat MeasureTheory Analysis Function Filter Metric Maxwell Finset Gap Complex Cauchy Row Phys Flux.One Lamp
open Lattice CF CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart CF.XGarden.MastTin.ArtCart.Violets CF.Py.Rate.LocalLimit.Papal
open scoped Topology ContDiff BigOperators Classical
open HopeC CF.Buffered CF.Buffered.Lifted
-- sum over stencil. unitaries factors. weights. arbitrary n0.
namespace Trackℓ
abbrev ΛN:= ℕ×ℕ×ℕ
def cN(i:ΛN):= i.1+i.2.1+i.2.2
def LaneB(t:ℕ):Finset ΛN:= (range (t+1))×ˢ ((range (t+1))×ˢ range (t+1))
lemma in_B (t:ℕ)(i:ΛN)(h:i∈ LaneB t) : cN i< 3*t+1:=by obtain ⟨a,p,q⟩:= i; simp only [LaneB,mem_product,mem_range] at h; unfold cN; dsimp only; omega
abbrev statW (t r:ℕ):=(LaneB t).filter (cN · = r)
variable (x: Cover)
abbrev eF (i:Wφ)(b:Bool)(t:ℕ):FW:= (tariff 1 t:ℂ) • boon (stride b) (pinF i) (Fuse x i) t
abbrev eG(i:Wα)(t:ℕ):PW:= (tariff 1 t:ℂ) • boon lace (pinG i) (Glint x i) t
abbrev σU(i: Chip)(v:ΛN): Book:= match i with
 | .litt a b=> if v.2.2=0 then αG (eG x a v.1) (eG x b v.2.1) else 0
 | .cuff a b=> if v.2.2=0 then αF (eF x a false v.1) (eF x b true v.2.1) else 0
 | .creel g a b=>αM (eG x g v.2.2) (eF x a false v.1) (eF x b true v.2.1)
-- constant.T. configure Move.
variable (t:ℕ)(a:ℝ)
lemma riv (r: ℕ): (a:ℂ)^r*(tariff 1 r:ℂ)=(tariff a r:ℂ):=by simp [tariff]
lemma milk_e(i:Wα): Gauke x i t a = ∑ j∈range (t+1),(a:ℂ)^j • eG x i j:=by simp [eG,riv, Gauke,Wane,smul_smul]; -- tune
lemma milk_h(i:Wφ)(b:Bool): Freight x i b t a=∑ j∈range (t+1),(a:ℂ)^j • eF x i b j:=by simp [eF,riv,Freight,Wane,smul_smul]
-- need Book channel injections linear
abbrev κgΛ: J GaugePair→ₗ[ℂ]Book:= (LinearMap.inr ..).comp (LinearMap.inl ..)
abbrev κfΛ: J Spair →ₗ[ℂ]Book:=(LinearMap.inr ..).comp ((LinearMap.inr ..).comp (LinearMap.inl ..))
abbrev κmΛ: J Trip→ₗ[ℂ]Book:=(LinearMap.inr ..).comp ((LinearMap.inr ..).comp (LinearMap.inr ..))
private lemma filterC {E:Type*} [AddCommMonoid E][Module ℂ E](f:ℕ→ℕ→E) :
 ∑ v∈LaneB t,(a:ℂ)^(cN v) • (if v.2.2=0 then f v.1 v.2.1 else 0)=∑ i∈range (t+1),∑ j∈range (t+1),(a:ℂ)^(i+j) • f i j:=by unfold LaneB; rw [sum_product]; simp_rw [sum_product]; simp [cN,Finset.sum_ite_irrel] -- tune smul ite
private lemma wireB {X Y Z:Type}[AddCommGroup X][Module ℂ X][AddCommGroup Y][Module ℂ Y][AddCommGroup Z][Module ℂ Z](f:ℕ→X)(g:ℕ→Y)(B:X→ₗ[ℂ]Y→ₗ[ℂ]Z):
 B (∑ j ∈range (t+1),(a:ℂ)^j • f j) (∑ j∈range (t+1),(a:ℂ)^j • g j)=∑ i∈range (t+1),∑ j∈range (t+1),(a:ℂ)^(i+j) • B (f i) (g j):=by simp_rw [map_sum B,LinearMap.sum_apply,map_sum,map_smul B,LinearMap.smul_apply,map_smul,smul_smul,pow_add]
lemma vault_σ (v:Chip): Lake a t x v=∑ k∈LaneB t, (a:ℂ)^(cN k) • σU x v k:=by
 cases v with
 | litt g h=>
    rw [Lake,milk_e,milk_e]
    exact (wireB t a _ _ (times'.compr₂ κgΛ)).trans (filterC t a (fun i j=> αG (eG x g i) (eG x h j))).symm
 | cuff g h=>rw [Lake,milk_h,milk_h]; exact (wireB t a _ _ (times'.compr₂ κfΛ)).trans (filterC t a (fun i j=> αF (eF x g false i) (eF x h true j))).symm
 | creel g u v=>
    rw [Lake,milk_h, milk_h, milk_e]; let F:=eF x u false; let G:=eG x g; let H:=eF x v true; let R:=range (t+1); let L:=times'.compr₂ κmΛ; let s (v:ℕ):ℂ:= (a:ℂ)^v
    change L (times' (∑ i∈R,s i • F i) (∑ i∈R,s i • H i)) (∑ j∈R,s j • G j)= _; rw [show times' _ _= _ from wireB t a F H times', map_sum L,LinearMap.sum_apply,LaneB,sum_product]; simp_rw [sum_product]
    apply sum_congr rfl; intro i _; rw [map_sum L,LinearMap.sum_apply]; apply sum_congr rfl; intro k _; rw [map_smul L,LinearMap.smul_apply,map_sum,smul_sum]; apply sum_congr rfl; intro j _; rw [map_smul,smul_smul]; change (s (i+k)*s j) • _= s (i+k+j) • _; rw [show s (i+k+j)= _ from (show _=s (i+k)*s j from pow_add ..)]; try rfl
variable {N:Side}
def sigΨ (v:Payν N)(k:ΛN) : Book:=∑ i:Eams v, Forces v i • σU v.1 (apices v i) k
def CrestJ(v:Payν N)(j:ℕ): Book:=∑ i∈statW t j,sigΨ v i
lemma prism_S (v:Payν N): RankBook a t v=∑ i∈ LaneB t,(a:ℂ)^(cN i) • sigΨ v i:=by
 unfold RankBook sigΨ; simp_rw [vault_σ v.1 t a, smul_sum]; rw [sum_comm]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; rw [smul_comm]
lemma prism_W (v:Payν N): RankBook a t v=∑ i∈range (3*t+1), (a:ℂ)^i • CrestJ t v i:=by
 rw [prism_S]; unfold CrestJ statW; simp_rw [smul_sum, sum_filter]; rw [sum_comm]; apply sum_congr rfl; intro i g; rw [sum_eq_single (cN i)]; simp; intro j _ e; rw [if_neg (Ne.symm e)]; exact fun p=> (p (mem_range.mpr (in_B _ _ g))).elim
-- eventual bounds.S
end Trackℓ
end YM.GaugeFieldConstruction.Wick.Yacht
end
