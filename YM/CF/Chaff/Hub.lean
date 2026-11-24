import YM.CF.Chaff.Pulse
import YM.CF.Char.Gel
import YM.Next.STATIONARY.Joint.OnShell
import YM.CF.Rill.Pott
import YM.CF.Skye.Hark
import YM.CF.Prism.Pecu
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Chaff
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory RG
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Kronecker
open Pressure
open Cube Lat Tenant Tulip Gully Spire Scroll Scree Jet Ave Skye Gas Pastry Dial Fock
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m B N: Side}{a e K H C:ℝ}{n:ℕ}
local notation "Λ" => CSide m B
local notation "ξ"=> Domain m B
local notation "G"=>SU.group
open Phase Branch
variable {D:Ave.Briar m B e→ Scree.Cipher (CSide m B)}{S:Stamp m B}
variable (p:0≤e)(h:Inscribed K e n S H D C)
local notation "Γ"=> tangD Λ
variable {s:ℝ}{R:Scree.Loom (CSide m B)}{P:BudgetPoint}{c:ℕ}(A:Roof (CSide m B) a s c R)(pH: P.threshold ≤ a)(v:s < e)(l:c≤P.B)
open MultiNext.SignedSource
variable (o:Seat (CSide m B))(y:o∈S) (t:Grove (terr _) S)
def riseH(P:BudgetPoint)(m:ℕ):=P.threshold*(1+m:ℝ)^P.power
def efflux(P:BudgetPoint)(X:Support (More N))(i:Seat N)(e:Skye.reach N): tangD N→L[ℝ] SU.group.Color := if e.1∈ X then Lyre.width P i e • ContinuousLinearMap.proj e else 0 -- tune ns
include t y
lemma life_s (P:BudgetPoint)(i:Skye.reach Λ):‖efflux P S o i‖ ≤ riseH P S.card:=by
 have hx:0 ≤ riseH P S.card:=mul_nonneg P.threshold_pos.le (by positivity)
 unfold efflux; split; swap; · rwa [norm_zero]
 next v=> apply ContinuousLinearMap.opNorm_le_bound _ hx; intro x; rw [ContinuousLinearMap.smul_apply,norm_smul,Real.norm_of_nonneg (Lyre.width_pos P _ _).le]; refine mul_le_mul ?_ (norm_le_pi_norm x i) (norm_nonneg _) hx; unfold riseH Lyre.width; have hu:= P.threshold_pos; gcongr; exact (t.lim _ v _ y).le
private def catchV(P:BudgetPoint)(X:Stamp m B)(o:Seat Λ): Γ→L[ℝ]Γ:= ContinuousLinearMap.pi (efflux P X o)
lemma tall_v (P:BudgetPoint): Allows n (catchV (m:=m) P S o) 0 (riseH P S.card):=by
 have ht:0≤riseH P S.card:=mul_nonneg P.threshold_pos.le (by positivity); apply allows_linear
 · refine ContinuousLinearMap.opNorm_le_bound _ ht fun x=>?_ ; apply (pi_norm_le_iff_of_nonneg (mul_nonneg ht (norm_nonneg _))).mpr; intro i; change ‖(efflux P S o i) x‖ ≤ _; exact ((efflux P S o i).le_opNorm x).trans (mul_le_mul_of_nonneg_right (life_s o y t P i) (norm_nonneg _))
 rw [map_zero,norm_zero]; exact ht
omit t y
lemma wind_p {v':ℝ}{Υ:Support (More N)}(u:Pane N)(X:tangD N→L[ℝ]tangD N)(p:pingS v' Υ u):∀ᶠ y:tangD N in 𝓝 0,pingS v' Υ (RG.increment u (X y)):=by
 let τ (y:tangD N):=RG.increment u (X y); have he:τ 0=u:=by unfold τ; rw [map_zero]; funext i; simp [RG.increment]
 have h:Continuous τ:=continuous_pi (fun i=> (SU.group.lieExp_cont.comp ((continuous_apply i).comp X.continuous)).mul continuous_const)
 exact (he ▸ h.tendsto 0 : Tendsto τ (𝓝 0) (𝓝 u)).eventually (ping_o.mem_nhds p) -- tune
local notation "Φ"=> pulseQ p R D P S
local notation "α"=> riseH P S.card
local notation "Ψ" V=> RG.increment V ∘ Prism.trunk P o
include A h l v pH
variable (q: P.order=n)
include p q
lemma girth_L (Z:Finset (Dwell Λ))(u:Pane Λ)(hp:1≤K)(v':pingS P.threshold (sailX P S) u): crumb (Φ u).val Z= crumb (D (polarU m B p (R (u,Classical.arbitrary _)))).val Z - if Z=∅ then Pastry.pane (D (floorP m B p)) else 0:=by
 unfold pulseQ; rw [Set.indicator_of_mem (show u∈_ from v')]; simp only [crumb]; change _- ((_:ℂ) • (1:FC (Dwell Λ))) Z ∅=_; by_cases e:Z=∅<;>simp [e,Matrix.one_apply] -- tune
include o t y
lemma trunk_p (U: Pane Λ)(u:pingS P.threshold (sailX P S) U)(τ:Ids Λ): let X:= R (U,τ); ∀ i:Γ, Agrees S ((Ψ U) i) (RG.increment X (catchV P S o i)) :=by
 intro V i j s k; unfold RG.increment; rw [show V j=U j from fare_H A pH l S U u τ j s k]; rw [show catchV P S o i j = efflux P S o j i from rfl, efflux,if_pos (by exact s)]; rfl
lemma expense (U:Pane Λ)(u:pingS P.threshold (sailX P S) U)(k:VStar n K)(g:1≤K)(k':1≤H)(Z:Finset (Dwell Λ)):
 Signs P o (fun i=> crumb (Φ (RG.increment U i)).val Z) ((composeCost n (H⁻¹^Z.card*C) α )+if Z=∅ then C else 0):=by
 obtain ⟨ε,f,s',w⟩:= toll_y v; let M:=catchV (m:=m) P S o; let x:=Classical.arbitrary (Ids Λ); let V:= R (U,x); have hv:Guard V s:= A.paid _; let J:= RG.increment V; let X:=fun i=>D (polarU m B p (J i)); let tH:=cosy p h k f s' V (w _ V hv); have hx: Allows n (fun i=> crumb (X (M i)).val Z) 0 (composeCost n (H⁻¹^Z.card*C) α) :=by
    have hp:‖M 0‖ < ε:=by rwa [map_zero,norm_zero]
    exact (cPick (A:=X) (tH (M 0) hp) (zero_lt_one.trans_le k') Z).comp (tall_v o y t P) -- tune b
 let c' := Pastry.pane (D (floorP m B p)); have ht: Allows n (fun _:Γ=> if Z=∅ then c' else (0:ℂ)) 0 (if Z=∅ then C else 0):=by
    apply allows_const; split_ifs; · have hz:= floorQ h g (floorP m B p) ∅ k'; rw [card_empty,pow_zero,one_mul] at hz; exact hz
    simp
 apply Prism.skills; rw [q]; refine (Newt.subtract_p hx ht).germ ?_; have hk:= trunk_p p h A pH v l o y t q U u x -- argument order
 filter_upwards [wind_p U (Prism.trunk P o) u,M.continuous.continuousAt.eventually (p:=fun v=>v∈ball (0:Γ) ε) (show ball (0:Γ) ε∈ 𝓝 (M 0) from by rw [map_zero]; exact ball_mem_nhds _ f)] with i y' e
 have hp:= hk i; have hu := base_P (y:=⟨J (M i),w _ V hv _ (mem_ball_zero_iff.mp e)⟩) p h A pH v l _ y' hp; change crumb (X (M i)).val Z-_=crumb (Φ _).val Z; unfold X; rw [claw p _ (w _ V hv _ (mem_ball_zero_iff.mp e)),hu]; unfold crumb; unfold c'; by_cases z:Z=∅<;>simp [z,Subalgebra.coe_sub, hollow,J] 
end YM.CF.Chaff
