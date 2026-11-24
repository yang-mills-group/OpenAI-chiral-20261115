import YM.CF.BProof.Prime.Levy
import YM.CF.BProof.Rise.Inside
import YM.CF.BProof.Oasis.Fee
/-! Prechoices for B-main, at fixed Gap and throughout this stage W. Frontier bound
on Earn and Tick bought BEFORE buying $h$, increasing allowance as necessary. Not
increasing $w_0$ thereafter. -/
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Start
open Function Filter Fock Finset NormedSpace Alignment -- tune
open Lattice Tenant Lat Cube Tulip Scree Skye Spin Branch Stint Hearth Tape Palot RG Push.AbsoluteSums Veil Oasis
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical Hearth
attribute [local instance] opCStarAlgebra
open Rhythm Jet Paige Drapes Vault Prime Estate Bias Cliff
variable {N:Side}{c:Clip}{w R v:ℝ}(S:Gates.Stage c w R v){m m' L B:Side}{j:ℕ} {a b l r:ℝ}{D:Spin.Ready j a b l r} {u:ℝ}(E:Essence D u)
variable {rₜ g:ℕ}(Δ: Rhythm.Note E g rₜ){p:Odd L.val} {Y:Pricing j L p (Vault.Thread j)}{δ:ℝ}(F:Grasp Y B δ)
abbrev Paint(m B:Side)(Z:Pec.Pride (mid m B))(a C:ℝ):=∀ x,Pec.cents (node x) (Z x) a ≤ C
-- Ready enough for aperture. purchase pig by $∀$ possible fields. spin gap not depends on h. 
structure Mote(X G:ℝ) where
 arc : Pay
 oak : Pay
 A:ℝ
 α:ℝ -- pig rate
 C:ℝ -- hum cost
 β:ℝ -- hum rate
 z:ℝ
 hp : 0< z
 zu : z ≤1
 ζ : Estate.Trust arc α β z
 k : ℕ
 pos : 0<k
 paid : Δ.clock.nearM ≤ k
 fuel : ℝ
 fuel_p : 0<fuel
 pigment {N:Side}{K:Core j a b l r (mid N B)}(O:Pec.Pride (mid N B))(H:Honor D K δ): Paint N B O X G→ F.roundZ ≤ (mid N B).val → Nonempty (Hinge F H Δ.stage.c Hero.rateH Δ.stage.η arc O (Economy.lipBill S.K.C) α A β C)
 gas {N:Side}{K:Core j a b l r N}(H:Honor D K δ) : Nonempty (Oasis.Marks H oak Δ.stage.c Hero.rateH Δ.stage.η)
 aperture : ∀ z':Fin 5, Bias.ScopeP g D δ Δ.stage.c Hero.rateH fuel k z'
-- namespace rateH Dream? check.
variable (J:1 ≤ j)(X G:ℝ)
include J
lemma clockEvent : Occasion Δ.stage.c Hero.rateH Δ.stage.η:=by
 exact ⟨Δ.stage.cE,Δ.stage.cP,Hero.expenses.one,Δ.stage.ηs⟩ -- check
lemma births(p:0<X)(v:0≤ G): Nonempty (Mote S E Δ F X G):=by
 let L:= Economy.lipBill S.K.C; obtain ⟨α,Jp,hα⟩:= Veil.pens L (Economy.bill_p _) v p; obtain ⟨β,U,hβ⟩:= Veil.hums F (Economy.bill_p S.K); obtain ⟨b,K⟩:= Tape.buys Hero.expenses.one Δ.stage.cE Δ.stage.ηp.le Δ.stage.ηs D δ; obtain ⟨Y,V⟩:= Oasis.chargeV D δ Hero.expenses.one Δ.stage.cE Δ.stage.ηp.le Δ.stage.ηs; obtain ⟨k,f,h₀,Hq⟩:= Bias.bought δ Δ.stage.c Hero.rateH D g J Δ.stage.cE Hero.expenses.one -- tune
 let u:= radF F; let z:=min (min (min 1 (b.rate/8)) (X/18/4)) (u/4); have hp:0<z:=lt_min (lt_min (lt_min zero_lt_one (div_pos b.charge (by norm_num))) (by positivity)) (by have hu: 0 < u:=rad_pos _; positivity); have hv:= min_le_left (min (min 1 (b.rate/8)) (X/18/4)) (u/4); have ht:= hv.trans (min_le_left ..);
 refine ⟨⟨b,Y,α,X/18,β,u,z,hp,ht.trans (min_le_left ..),⟨hp.le,by linarith only [show z≤ b.rate/8 from ht.trans (min_le_right ..)],by linarith only [show z≤ X/18/4 from hv.trans (min_le_right ..)], by linarith only [show z≤ u/4 from min_le_right ..]⟩,1+k+Δ.clock.nearM,by omega, by omega,f,h₀,?_ ,?_,fun z=> Bias.ScopeP.up z (Hq z) (by omega) le_rfl⟩⟩
 · intro m F' Q H ht p; obtain ⟨fP⟩:=hα m _ Q δ ht; obtain ⟨dP⟩:= hβ m F'.M p; exact Veil.ropes F (clockEvent E Δ J) (K H) fP dP -- tune
 exact V
end YM.CF.BProof.Start
