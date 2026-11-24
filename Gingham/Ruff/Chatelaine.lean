import Gingham.Ruff.Pleat
import YM.CF.Sour.Lead
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Finset Fock Scree Pastry
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Lattice Wilson Laurent Cube SU Lat Spire Scroll Peaks Drapes Rush Precision Tulip Jet
    Tap Laic Dial Paige Vault Pec Skye Branch
variable {N:Side}

open RG Vow Hake Tenant
set_option linter.unusedSimpArgs false


open Sour Rill
attribute [local instance] Rill.boreKSpace Rill.boreXN Sour.loreM Sour.loreN

/-- Pointwise credential in lattice paid regions: local at all final cleared consultations,
angular at any such with any superset deletion. price is entered as base cost; pay extra
(order+1)=7 globally to retrieve full Pence. Note X is the footprint for lit, not merely
the groove witnessing a holomorphic entry. -/
structure WearL (p:BudgetPoint)(r:ℕ)(X:Support (More N))
    (A:Orbit N→OP N)(w:Toll (Single N)):Prop where
  floor : ∀ i j, 0≤w i j
  ambient(i j:Single N): w i j≠0 → node i.1.1 ∈ X ∧ node j.1.1 ∈ X
  value (x:Orbit N)(i j:Single N): ‖A x i j‖ ≤ w i j
  borel:Measurable A
  tint(x:Orbit N)(t:Seat N→SU.E):
    A (Lattice.gauge t x.1,threadG t x.2)=twist (tradew N t) (A x)
  same {Y:Aura N}{D:Support (More N)}(x y:Orbit N):
    X ⊆ Y.val → Lattice.halo (cipherK r) D ⊆ Y.val →
    x.1∈σX p Y D → y.1∈σX p Y D →
    Agrees Y.val x.1 y.1 → Set.EqOn x.2 y.2 Y.val → A x=A y

  paid {Y:Aura N}{D Z:Support (More N)}(x:Orbit N):
    X ⊆ Y.val → Lattice.halo (cipherK r) D ⊆ Y.val →
    x.1∈σX p Y D → D⊆Z →
    ∀i j,Pence p.order (fun v:tangD N=>A (pressQ p Z x.1 v,x.2) i j) 0
       ((p.order+1:ℝ)*w i j)

structure Briefly (p:BudgetPoint)(r:ℕ)(e:ℝ)(U: Scree.Loom N) : Prop where
  pos : 0<e
  roof : ∃t, p.threshold≤t ∧ Roof N t e r U
  hope : ∃m a, p.threshold≤a ∧ HopeT e m a p.order
  key : cipherK r ≤ 5 * p.B
  heat : 3 ≤ p.B

namespace Briefly
variable {p:BudgetPoint}{r:ℕ}{e:ℝ}{U: Scree.Loom N}(h:Briefly p r e U)
def depth := h.roof.choose
lemma ceiling: p.threshold≤ h.depth ∧ Roof N h.depth e r U:= h.roof.choose_spec
def roll:= roller h.pos h.ceiling.2
lemma clears {S:Support (More N)}
    {F:Fob N e}{W:Toll (Single N)}
    (g:Suite (badge (Openc (More N) e)) (bail N e) (bail N e) S W F):
    WearL p r (Lattice.halo (r+10) S) (F∘h.roll) W :=by
  obtain ⟨m,a,j,k⟩:=h.hope
  refine ⟨g.nonn,?_, fun x i j=>(g.expo i j).bounded _,?_,?_,?_,?_⟩

  · intro i l t
    obtain ⟨_,b,v⟩:=(g.expo i l).triggered t
    exact ⟨halo_subset _ _ b,halo_subset _ _ v⟩
  · exact g.cont.measurable.comp (Rill.roll_m h.pos h.ceiling.2)
  · intro x t
    simp only [comp_apply,roll,roll_g,g.frame.frame,twist_formula]
    rfl
  · intro Y D x y v w s a z l
    exact pact_p h.pos h.ceiling.2 g _ _
      (Rill.poli h.ceiling.2 h.ceiling.1 w s S v a z l)
  intro Y D Z x v w a0 l i o
  exact Rue.bare_p _ _ (Rill.earn_b h.pos h.ceiling.2 h.ceiling.1 g k _ Y v j w h.key h.heat a0 l i o)
end Briefly




variable {p:BudgetPoint}{r:ℕ}{A:Orbit N→OP N}{w:Toll (Single N)}
   {X M T:Support (More N)}(g:WearL p r X A w)

open scoped Classical
open Filter

/-- Masked or complementary deactivation receipts. On clears they are exact,
  not paying for either choice of final D in the summations. -/
def retina (p:BudgetPoint)(M: Support (More N))(x:Orbit N):Bool:=
  if pingS p.threshold M x.1 then true else false
def silkcut (p:BudgetPoint)(M:Support (More N))(β:Bool)(A:Orbit N→OP N):Orbit N→OP N:=
  fun x=> if retina p M x=β then A x else 0

lemma curtain (p: BudgetPoint){Y:Aura N}{D:Support (More N)}
    (x:Orbit N)(h:M⊆Y.val)(k:x.1∈σX p Y D):
    retina p M x = true ↔ Disjoint M D:=by
  simp only [retina,ite_eq_left_iff,Bool.false_eq_true,imp_false,not_not]
  constructor
  · intro t; exact (ping_le t).mono_right k.2
  intro a
  exact Vow.grow_b (show M⊆Y.val\D from fun i l=>mem_sdiff.mpr ⟨h l, disjoint_left.mp a l⟩) k.1

lemma curtains (p:BudgetPoint){Y:Aura N}{D:Support (More N)}(x y:Orbit N)(h:M⊆Y.val)
    (k:x.1∈σX p Y D)(u:y.1∈σX p Y D):retina p M x=retina p M y:=
  by simp [Bool.eq_iff_iff,curtain p x h k,curtain p y h u]


lemma curtain_near (p:BudgetPoint){Y:Aura N}{D:Support (More N)}(x:Orbit N)
  (Z:Support (More N))(h:M⊆Y.val)(k:x.1∈σX p Y D):
    ∀ᶠ z:tangD N in 𝓝 0, retina p M (pressQ p Z x.1 z,x.2)=retina p M x:=by
  have t:Tendsto (pressQ p Z x.1) (𝓝 0) (𝓝 x.1):=by
    have tq:= ((Forge.stickU (Rill.unrest Z p.B) x.1).comp (continuous_id.const_smul p.threshold)).tendsto 0
    change Tendsto (pressQ p Z x.1) (𝓝 0) (𝓝 (pressQ p Z x.1 0)) at tq
    have z:pressQ p Z x.1 0 = x.1:=by unfold pressQ;rw [smul_zero,Forge.born]
    rwa [z] at tq
  exact (t.eventually ((Rue.open_l ..).eventually_mem k)).mono fun z i=>
    (curtains p x (pressQ p Z x.1 z,x.2) (Y:=Y) (D:=D) h k i).symm

lemma retinaM (p:BudgetPoint)(M: Support (More N)): Measurable (retina p M):=
  Measurable.ite (measurable_fst ping_o.measurableSet) measurable_const measurable_const

include g
lemma veil(β:Bool)(u:X⊆T)(m:M⊆T): WearL p r T (silkcut p M β A) w:=by
  refine ⟨g.floor,fun i j t=>
    ⟨u ((g.ambient i j t).1),u ((g.ambient i j t).2)⟩,
    ?_,Measurable.ite (measurableSet_eq_fun (retinaM p M) measurable_const) g.borel measurable_const,?_,?_,?_⟩
  · intro x i j
    unfold silkcut; split; exact g.value _ _ _
    simpa using g.floor i j
  · intro x t
    unfold silkcut retina
    dsimp only
    rw [pingB]
    split_ifs <;> first | exact g.tint x t | exact (map_zero _).symm

  · intro Y D x y v w b c i z
    unfold silkcut; rw [curtains p x y (m.trans v) b c]
    split;exact g.same _ _ (u.trans v) w b c i z
    rfl
  intro Y D Z x v wt c d i j
  have ne:=curtain_near p x Z (m.trans v) c
  by_cases t: retina p M x=β
  · exact (g.paid x (u.trans v) wt c d i j).germ (ne.mono fun a l=>by simp [silkcut,l,t])
  have tt:Pence p.order (fun _:tangD N=>(0:ℂ)) 0 ((p.order+1:ℝ)*w i j):=by
    have q:= Pence.const (k:=p.order) (0:tangD N) (0:ℂ)
    exact ⟨q.smooth,q.earned.trans ((show ‖(0:ℂ)‖=(0:ℝ) from norm_zero).le.trans
      (mul_nonneg (by positivity) (g.floor i j)))⟩
  exact tt.germ (ne.mono fun a l=>by simp [silkcut,l,t])

lemma WearL.mono(u:X⊆T): WearL p r T A w :=
  ⟨g.floor,fun i j t=> ⟨u ((g.ambient i j t).1),u ((g.ambient i j t).2)⟩,g.value,g.borel,
    g.tint,fun x y p=>g.same x y (u.trans p), fun x y=>g.paid x (u.trans y)⟩

#print axioms veil
