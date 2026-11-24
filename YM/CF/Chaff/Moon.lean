import YM.CF.Chaff.Echo
import YM.CF.Fief.Lucid
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
variable {r Y V x μ b θ C' ρ:ℝ} {M:ℕ}
structure Nice (n:ℕ)(P:BudgetPoint)(e K C0 ε:ℝ):Prop where
 orderX : P.order=n
 inflow:12 ≤P.B
 guardP : ∃ b:ℝ,0<b∧ b≤1∧ ε≤ b/2∧∀ (m B:Side)(i:tangD (CSide m B)), ‖i‖< b→Guard (RG.increment 1 i) e
 test: ∃ d:ℝ,dex C0 d∧ black_t P ≤ d
 purse : 0 ≤ C0
 arcs : ∃ k r:ℝ,0<k∧0<r∧ ε=r*leanP P C0 ∧ Brink n k r∧ leanP P C0 ≤ k
 knot : VStar n K
 κ : 1≤ K
abbrev neatP(P:BudgetPoint)(x:Scree.Hub N):Scree.Hub N:=⟨(x.val.1,taleX P x.val.2),halo_subset _ _ x.property⟩ -- tune
local notation "Y'"=> (pulseQ p R D P S)
variable (N':Nice n P e K C' θ)(k':1≤H) (Yf:0≤Y)(W0:0≤μ)(X0:0≤r)(p':r≤1)(L:Y* H⁻¹ ≤ r * μ)(q:μ * mealz ≤ b)(T: 4*P.B < (Domain m B).val)
include A pH v l h N' k' Yf W0 X0 p' L q T y
lemma Burn_p : PressB P (n:=Λ) (neatP P ⟨(o,S),y⟩) Y' Y (cliff (m:=m) (B:=B) P b C θ μ r S):=by
 have hp0:0<H:=zero_lt_one.trans_le k'
 by_cases k:C=0
 · have he:D=0:=funext fun i=>by
    apply Ione.pimp_Q; intro j; change crumb (D i).val j=crumb (0:FC _) j; have hv:=floorQ h N'.κ i j k'; rw [k,mul_zero] at hv; change crumb _ _=0; exact norm_le_zero_iff.mp hv
   rw [he, k, show pulseQ p R (0:Briar m B e→Cipher Λ) P S=0 from ?_,show cliff (m:=m) P b 0 θ μ r S=0 from ?_]; exact Vale.rinse ..; swap
   · funext i; unfold pulseQ; by_cases p:i∈{U|pingS P.threshold (sailX P S) U}; rw [Set.indicator_of_mem p]; apply Subtype.ext; change (0:FC _)- (Pastry.pane (0:Dough (Dwell Λ)) • 1)=0; rw [show Pastry.pane (0:Dough (Dwell Λ))=(0:ℂ) from rfl,zero_smul,sub_zero]; exact Set.indicator_of_notMem p _ -- tune cases
   unfold cliff taxH; split<;> simp [composeCost]
 have hu:=h.grove k; let Z:=levyP m B P S C H θ
 refine ⟨currentX p h A pH v l N'.inflow,fun X=> (φs_b p h A pH v l X).lift ?_,pulse_m p h A pH v l, φs_g p h A pH v l,⟨Z,levy_pos P S h.pos hp0 _,fun U hx X=>?_,shootB S Yf hp0 μ W0 X0 p' L h.pos 0 b θ q o y hu⟩⟩
 · intro i u; exact mem_filter.mpr ⟨mem_univ _,halo_subset _ _ (mem_filter.mp u|>.2)⟩
 let x':= RG.increment U; change Signs _ o _ (Z X); let Z' := Y'; have hQ:=N'.orderX; have hy:= Vow.grow_b (arms_e S) (show pingS P.threshold (taleX P S) U from hx)
 unfold Z levyP; split_ifs with u eA
 · rw [u]; unfold taxH; split_ifs with kL
   · obtain ⟨d,hD,hB⟩:=N'.test; obtain ⟨j,r,jQ,rQ,w1,k',J⟩:= N'.arcs; obtain ⟨g,hG,gK,h0,W⟩:=N'.guardP; rw [w1,hQ]; rw [w1] at h0; exact scent_C p h A pH v l o y hu N'.purse hD hB hQ k' rQ J N'.knot hp0 hG gK (W m B) h0 U hy kL T
   have ht:= expense p h A pH v l o y hu hQ U hy N'.knot N'.κ k' ∅; simpa only [←hQ,↓reduceIte,card_empty,pow_zero,one_mul] using ht
 · have ht:= expense p h A pH v l o y hu hQ U hy N'.knot N'.κ k' X; simpa only [←hQ,if_neg u,add_zero,buyT] using ht
 apply Prism.mint (A:=fun _=> (0:ℂ)) _ _; · exact Prism.hail (show ‖(0:ℂ)‖ ≤ 0 from norm_zero.le)
 exact Eventually.of_forall fun i=> Eq.symm ((φs_b p h A pH v l (x' i)).door (fun v=> eA (mem_powerset.mp (mem_filter.mp v).1))) -- namespace n implicit tune
end YM.CF.Chaff
