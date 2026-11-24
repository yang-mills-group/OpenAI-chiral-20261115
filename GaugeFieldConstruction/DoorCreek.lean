import GaugeFieldConstruction.Hamat
import GaugeFieldConstruction.Solvent
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Heat
open Etch
namespace Weir
section doors
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
local notation "L₀"=>Λ.R.L.val
local notation "m" n:max s:max=>momentm Y n s
local notation "T₀" n:max s:max=> Journey.side Y n s
local notation "B₀"=> Λ.block.val
local notation "κ"=> (Y.tile*Λ.M).val
def tierW :ℤ:= if Odd ((Y.tile*Λ.M).val) then 2*(Λ.block.val:ℤ) else 4*(Λ.block.val:ℤ)
lemma tierW_pos:0<tierW Y:=by have t:=Λ.block.property; unfold tierW; split <;> positivity
-- W measured directly in integer gauge pitches. a arbitrary power at this level;
-- lifted-higher from lower still qualifies if W of this form.
def westW (a:ℕ):= tierW Y*(Λ.R.L.val:ℤ)^a
lemma westW_pos (a:ℕ):0<westW Y a:=mul_pos (tierW_pos Y) (by positivity)
def chute (σ:Cover):Prop:=∀ i, tierW Y ∣ σ i
lemma water_paid (σ:Cover)(u:chute Y σ)(s a:ℕ):∀ᶠ i:ℕ in atTop,∃ n:Side,LatticeFare K (m i s) n (westW Y a) σ:=by
 let y(i):=Y.stage i+s-a
 let t := Λ.block.val
 filter_upwards [Y.infrared.tendsto_atTop.eventually (eventually_ge_atTop a)] with i p
 have ht:a+y i=Y.stage i+s:=by unfold y; omega
 let V:= (m i s); let x:=(K).c V -- local macro bad
 have he:x.val=2*t*κ*L₀^(a+y i) :=by
    unfold x; rw [side_register,ht,pow_add]
    change ((Journey.side Y i s).val)=_
    have P':(m i s).val= κ* L₀^ (Y.stage i)*L₀^s:=by change ((Vale.mesh (Vale.mesh (Y.tile*Λ.M) Λ.R.L (Y.stage i)) Λ.R.L s).val)=_; unfold mesh; push_cast; rfl
    change ((m i s).val*2)*Λ.block.val=_
    rw[P']; unfold t; ring
 by_cases h:Odd κ
 · let n:Side:= (Y.tile* Λ.M)* Λ.R.L^ (y i)
   have hu:n.val=κ* L₀^ (y i):=by unfold n; push_cast; rfl
   have w:tierW Y=2*(t:ℤ):=by unfold tierW; rw [if_pos h]
   have k: (x.val:ℤ) = westW Y a*(n.val:ℤ):=by unfold westW; rw[w,he,hu]; push_cast; ring
   refine ⟨n,westW_pos Y a,k,fun j b=>?_⟩
   obtain ⟨d,hp⟩:=u j
   have P:bank σ (westW Y a) b j= (2*t:ℤ)*(d+ ((Λ.R.L.val:ℤ)^a)*b):= by unfold bank westW; rw [hp,w]; ring
   let r:=d+((Λ.R.L.val:ℤ)^a)*b
   change ( _= (2*t:ℤ)*r) at P
   have T:Odd (κ* L₀^(a+y i)):=h.mul (Λ.R.odd_side.pow)
   let g:=κ* L₀^(a+y i)
   change Odd g at T
   by_cases hh:Even r
   · left; obtain ⟨v,q⟩:=hh; refine ⟨v,?_⟩; change _=4*(t:ℤ)*_; rw[P,q]; ring
   have hz:Odd r:=Int.not_even_iff_odd.mp hh
   have hQ:Odd (g:ℤ):=by exact_mod_cast T
   obtain ⟨v,q⟩:=hz.add_odd hQ
   refine Or.inr ⟨v,?_⟩
   calc bank σ (westW Y a) (b + n.val) j = bank σ (westW Y a) b j +(x.val:ℤ):=by unfold bank; rw [k]; ring
        _= (2*t:ℤ)*(r+g):=by
            have hδ : x.val=2*t*g:=by unfold g; rw [he]; ring
            rw[P,hδ]; simp only [Nat.cast_mul,Nat.cast_ofNat]; ring
        _= gaugeShift (K).B v:=by rw[q]; change _=4*(t:ℤ)*_; ring
 have hγ: Even κ:=Nat.not_odd_iff_even.mp h
 obtain ⟨d,q⟩:=hγ
 have hp:0<d:=by have h':0<κ:=(Y.tile*Λ.M).property; omega
 let n:Side:= ⟨d*L₀^(y i),by positivity⟩
 have u' : tierW Y=4*(t:ℤ):=by unfold tierW; rw[if_neg h]
 refine ⟨n,westW_pos Y a,?_,?_⟩
 · change (x.val:ℤ)=(westW Y a)*((↑(d*L₀^(y i))):ℤ); rw[westW,he,u',q]; push_cast; ring
 intro j b; left; obtain ⟨z,rfl'⟩:=u j; refine ⟨z+(Λ.R.L.val:ℤ)^a*b,?_⟩; change _=4*(t:ℤ)*_; unfold bank westW; rw [rfl',u']; ring
#print axioms water_paid
end doors
end Weir
end YM.CF.Buffered.Afterglow.Tower.SlabMark
