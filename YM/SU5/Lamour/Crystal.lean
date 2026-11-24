import YM.SU5.Lamour.Poise
/-! # Crystalline Moth. neighborhood & geometry.
 For caller wanting only first orientation, condition even both links near; from flag-free solve for both.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 280000
noncomputable section
namespace YM.CF.Lamour.Bridge
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Scree CF.Pannier.Damask Buffered Branch Tenant Skye Pannier.Chancel Brace Velvet Hours Flare Cliplet RG Reed Py.Rate.Pannier
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {N: Side}{j d r n k a w:ℕ}{ε ξ δ z l v θ γ ζ μ τ ν C B:ℝ}{M:Tulip.Male}{U: Loom N}
structure LocalTune (j d r:ℕ)(ε ζ C B:ℝ)(N:Side)(M:Male)(F:Mark N)(o:Seat N)(S:Finset (Seat N)):Prop where
 color: covariant F
 range: AtSupport false S F
 units: ∀ X:Fields N,‖F X‖≤ C
 pin : o ∈ S
 border : S⊆BlockP r o
 issued : (modesIn N S).card≤ d
 limit: ∀ X:Fields N, Rightful S X.1 1 ζ→Rightful S X.2 1 ζ→ ‖F X-F (1,1)‖≤ ε
 reads: ∃ x,Sea (spar j M (1:Pane N)) x∧ ‖alleyR (mateK N) x (F (1,1))‖≤ B/4
variable {o:Seat N}{S:Finset (Seat N)}{F:Mark N}{P V:Pane N}{s t u:ℕ}
local notation "Ⲙ" => Lattice.halo
lemma fit (p:S⊆BlockP r o): (Ⲙ w S)⊆BlockP (r+w) o:=by
 intro i h; obtain ⟨k,u,v⟩:=halo_spec.mp h; exact blocks_test.mpr ((separation_triangle ..).trans (add_le_add (blocks_test.mp (p u)) v))
lemma rect (p:Rightful S V 1 γ)(h:Agrees S P V):Rightful S P 1 γ:=by
 apply (riotPort S P 1).2; intro i q; rw [h i (mem_filter.mp q).2.1 (mem_filter.mp q).2.2]; exact (riotPort S V 1).1 p _ q
/-- fix class before N history requirements. r:Mark. h:after Clear requirements. mark and hire ζ supplied. -/
def Warrant(r h:ℕ)(γ:ℝ)(ζ:ℝ)(τ:ℝ):Prop:=∀ {N:Side}{o:Seat N}{X:Pane N}, (2*((r+h)+1)<(More N).val)→ Disjoint (BlockP ((r+h)+1) o) (flags τ X) → Rightful (BlockP (r+h) o) (Lattice.gauge (stampG o X) X) 1 (min γ ζ)
lemma point_of_purchase (p:0<γ)(t:0<ζ)(r h:ℕ):∃ x>(0:ℝ),∀ y,0≤y→y≤x→Warrant r h γ ζ y:=by
 obtain ⟨x,u,H⟩:= stampG_price (r+h) (min γ ζ) (lt_min p t); exact ⟨x,u,fun y p q _ _ _ g ht=>H y p q g le_rfl _ _ ht⟩ -- tune {N}
variable (H:Optic j n k d v ε θ l C B)(q:Procurement j a δ)(W:Warrant r s γ ζ τ)(roof: Roof N μ δ t U)
-- from DIRTY split all clean
include H q W roof
lemma preen (H₁:Kea.Pad j N)(h:n≤N.val)(p:a≤N.val)(z0:0<z)(z1:z≤1)(c: ClothQ a j δ z ε γ s)(a':Closen j z ε)(x:Orbit N)(hx: τ≤μ)(ht:2*((r+s)+1)<(More N).val)(L:LocalTune j d r ε ζ C B N M F o S)(g:Disjoint (BlockP (((r+s)+1)+t) o) (flags τ x.1)):
 let D:= modesIn N S; let P:=U x; let A:=here N j z M P; let V:= slant (cutM (Tset N)) A z
 (Bun (ray V (Tset N)) D D l)∧(∀ X:Finset (Seat N),Distant (k+1) X S→Bun (ray V (Tset N)) (modesIn N X) D v)∧
 (∀ i∈ D, ‖acts (wish (tickA N) A z (shadeK (Tset N) i)) (basisKet i)‖ ≤ v) ∧ (∀ X: Wave (Single N), Sea A X → ‖F (x.1,P)‖*(4*v)*(4*l)^d + ‖boomR X (cutM_idp (Tset N)) z0 (F (x.1,P))‖≤ B):= by
 let R:=r+s; let Y:= R+1; let ω:=stampG o x.1; let Λ:=BlockP R o; let A':=Lattice.gauge ω (U x); let P':=Lattice.gauge ω x.1; let G:= flags τ x.1; have he: S ⊆ Λ:= subset_trans L.border (Corona.halo_mono (Nat.le_add_right ..) subset_rfl)
 have hy: Agrees Λ (U x) x.1:=fledged roof Λ x hx (Disjoint.mono_left (by apply subset_trans (fit (subset_refl Λ)); exact Corona.halo_mono (Nat.add_le_add_right (Nat.le_add_right R 1) t) subset_rfl) g)
 have hr:Agrees Λ A' P':= tied _ _ _ _ _ hy (fun _ _=> rfl) -- EqOn
 have hc: Rightful Λ P' 1 (min γ ζ):= W ht (Disjoint.mono_left (Corona.halo_mono (Nat.le_add_right Y t) subset_rfl) g)
 have hh:= rect hc hr; intro D P A V; have hg: Guard P δ:= roof.paid x; have hW:Guard A' δ:= hg.cov ω
 have hp:= purchase q z0 z1 H₁ p c a' hW (loft_rightful (P:=A') hh (min_le_left ..) (show (Ⲙ s S)⊆Λ from fit L.border)) M;
 have hv:= q.audit (M:=M) p; obtain ⟨n0,hT,m_⟩:= Optic.reach H H₁ h S hv hg z0 z1 ω hp; have hV:V=sill N j M z P:=by unfold V; rw [←touchP]; rfl
 rw [hV]
 refine ⟨n0,hT,m_,fun X p=>?_⟩
 let F':= F (x.1,P)
 let γ:=tradew N ω
 let f0:Fields N:=(x.1,P); let x1:=simultaneous ω f0
 let Z':= acts (quantU γ).val X
 have hZ:Sea (here N j z M A') Z':=by unfold A' here; rw [account_cov hv hg ω z0 z1]; exact lifted γ p
 have hgX: F x1=twist (quantU γ) (F f0):= L.color ω f0
 have hv1: Rightful S x1.1 1 ζ:=loft_rightful hc (min_le_right ..) he; have hv2: Rightful S x1.2 1 ζ:= loft_rightful hh (min_le_right ..) he
 have hρ:=H.port S (F (1,1)) (F x1) (L.units x1) (L.limit x1 hv1 hv2) L.issued (L.range.allV x1) (L.range.allV (1,1)) H₁ hv hW z0 z1 hp L.reads Z' hZ
 rw [hgX, twist_norm] at hρ; rw [show boomR Z' (cutM_idp (Tset N)) z0 (twist (quantU γ) (F f0)) = boomR X (cutM_idp (Tset N)) z0 (F f0) from held (cutM_idp _) (gauge_frostT ω) z0 X (F f0)] at hρ; exact hρ
omit H q W roof
lemma flightPhys (F:Mark N)(S T:Finset (Seat N))(h:AtSupport false T F)(u:T⊆ S):∀ X:Fields N,Fine (Tset N) (modesIn N S) false (F X):=(h.mono u).allV
variable {I:Type*}[Fintype I][LinearOrder I]
lemma wind_flight (Z:I→Finset (Seat N))(L:Finset I)(p:∀ i∈L,∀ j∈L,i≠j → Distant (k+1) (Z i) (Z j)): (↑L:Set I).PairwiseDisjoint (fun i=> modesIn N (Z i)) := by
 intro i q j x h; refine Finset.disjoint_left.mpr fun x y g=>?_ ; have ht:=p i q j (by assumption) h _ ((modes_at ..|>.1 y)) _ (modes_at ..|>.1 g); rw [separation_self] at ht; omega
lemma flown (Z:I→Finset (Seat N))(L: Finset I)(p:∀ i∈L,∀ j∈L,i≠j → Distant (k+1) (Z i) (Z j)) (i:I)(w:i∈L): Distant (k+1) ((L.erase i).biUnion Z) (Z i):= by intro x q; obtain ⟨y,u,h⟩:=mem_biUnion.mp q; exact p y (mem_of_mem_erase u) i w (mem_erase.mp u|>.1) x h
lemma flown_modes (Z:I→Finset (Seat N))(L:Finset I): (L.biUnion fun i=>modesIn N (Z i)) ⊆modesIn N (L.biUnion Z):=by
 intro i h; obtain ⟨j,k,v⟩:=mem_biUnion.mp h; exact (modes_monotone (subset_biUnion_of_mem Z k)) v
include H q W roof
lemma poised (H₁:Kea.Pad j N)(h:n≤N.val)(p:a≤N.val)(z0:0<z)(z1:z≤1)(c: ClothQ a j δ z ε γ s)(a':Closen j z ε)(x:Orbit N)(hx: τ≤μ)(ht:2*((r+s)+1)<(More N).val)(o:I→Seat N)(S:I→Finset (Seat N))(F:I→Mark N)(i:Finset I)(H0:∀ j'∈ i, LocalTune j d r ε ζ C B N M (F j') (o j') (S j'))(p0:∀ x∈i,∀ y∈i,x≠y →Distant (k+1) (S x) (S y))(g: ∀ j ∈i,Disjoint (BlockP (((r+s)+1)+t) (o j)) (flags τ x.1))(y:Wave (Single N))(f:Sea (spar j M (U x)) y)(Z:FC (Single N)):
 let P:= U x; let A:= spar j M P; let G:=tickA N;
 Yep ((z*v)⁻¹*flowCost z) (acts (star (Z*fo (fun i=>F i (x.1,P)) (i.sort (· ≤ ·)))) (mateK N)) y (‖modifyB G z Z‖*(B^i.card)*Real.exp (trade A G z)):=by
 intro P A G; let V:= here N j z M P; let S':= fun i'=> modesIn N (S i'); let ℓ(v)(x:v∈ i):= (H0 v x).range; have hg:=fun j hj=> preen H q W roof H₁ h p z0 z1 c a' x hx ht (H0 j hj) (g j hj)
 unfold G; rw [touchP, ←prod_const B (s:=i)]; let Y':= cutM (Tset N); have he : IsStarProjection A:=(q.audit p).projection _ (roof.paid x);  -- tune
 have hp:V=draft A Y' z:=by unfold V here; rw [touchP]
 refine Trees S' _ i he f.2 f z0 z1 (tick_cut N) _ Z rfl H.genuine H.low (wind_flight S i p0) H.lip d (fun j w=> (H0 j w).issued) (fun j w=> (H0 j w).range.allV _) ?_ ?_ ?_ (fun _=>B) ?_ -- d shadow fix
 · intro j w; let X:= Z; rw [←hp]; intro y v; let ht:= (hg j w).2.1 _ (flown S i p0 j w) y v; exact ht.trans' (sum_le_sum_of_subset_of_nonneg (flown_modes S _) (fun _ _ _=> by positivity))
 · intro j w; rw [←hp]; exact (hg j w).1
 · intro j w; let hc:= (hg j w).2.2.1; rw [←hp, ←touchP]; exact hc
 intro j w; rw [←hp]; exact (hg j w).2.2.2
end YM.CF.Lamour.Bridge
#print axioms YM.CF.Lamour.Bridge.poised
