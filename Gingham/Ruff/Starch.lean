import YM.CF.DPress.Plaque.Taps
import Gingham.Ruff.Flares
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
open scoped Classical


variable {y:Site N}{u:Side}{l r:ℕ}{E q e a c:ℝ}{p:BudgetPoint}{U:Scree.Loom N}
variable (g:Briefly p r e U)
variable (G:Tagbill a E u l r p.B)


lemma pingWide {d t:ℝ}{M:Support (More N)}{X:Pane N}(h:pingS d M X)(l:d≤t):
  pingS t M X:=fun a v=>(h a v).trans_le l

lemma halo_spread {o:Site N}{S:Support N}{s t z:ℕ}
    (h:∀ i∈S,separation o i ≤ s)
    (p:t+s≤z): Lattice.halo t S ⊆ Lattice.halo z {o}:=by
  intro i b
  obtain ⟨a,u,f⟩:=halo_spec.mp b
  refine halo_spec.mpr ⟨o,mem_singleton_self _,(separation_triangle o a i).trans ?_⟩
  exact (Nat.add_le_add (h a u) f).trans (by omega)

abbrev belle (y:Site N)(b:ℕ):= hoop y (b/10)
lemma innerlude (y:Site N)(b:ℕ): belle y b ⊆ hoop y b:=
 Corona.halo_mono (by omega) le_rfl

section halo
include G
lemma girder_l (S:Support (More N))(x:Girder y u S)(w:S.card≤ tenderb p.B):
 Lattice.halo (r+10) S ⊆ belle y p.B:=
 halo_spread x (by unfold tenderb at w;have :=G.largeB;omega)

lemma girder_i (S:Support (More N))(x:Girder y u S)(w:S.card≤ tenderb p.B):
  S⊆belle y p.B:=(halo_subset _ _).trans (girder_l G S x w)

end halo


include g G
lemma pilotL {S:Support (More N)}(h:Lattice.halo (r+10) S ⊆ belle y p.B)
    (x:Orbit N)(v: pingS p.threshold (hoop y p.B) x.1): Agrees S (U x) x.1:=by
  have hv:=ping_le (pingWide v g.ceiling.1)
  intro i a b
  refine g.ceiling.2.lamp x.1 x.2 i
    (hv.symm.mono_right ((Corona.halo_mono (by omega:r≤r+10) ?_).trans
      (h.trans (innerlude y p.B))))
  exact insert_subset a (singleton_subset_iff.mpr b)
omit g G

lemma fare_swap {S: Support (More N)} {X X' V V':Pane N}
    (h:Agrees S X X')(p:Agrees S V V'):
    fare S (profile X) (profile V)=fare S (profile X') (profile V'):=by
  apply sum_congr rfl; intro i t
  obtain ⟨a,b⟩:=(mem_filter.mp t).2
  unfold profile;rw [h i a b,p i a b]

lemma fare_cyl {S: Support (More N)} {X V:Pane N} (h:Agrees S X V):
    fare S (profile X) (profile V)=0:=by
  rw [fare_swap h (fun _ _ _ =>rfl)]
  simp [fare]

variable {A:Fob N e}
variable (H:Plastron y u e (a/4) c A)

abbrev tagged := tagLite (b:=p.B) H -- p implicit


abbrev silkT:= silkcut p (hoop y p.B)


def touchprice (p:BudgetPoint) (i j:Single N):= ∑ S,(tagLite (b:=p.B) H).cost S i j

include G H g
lemma afternoon (x z: Orbit N)(t:pingS p.threshold (hoop y p.B) x.1)
    (v:pingS p.threshold (hoop y p.B) z.1)(i j: Single N):
    ‖liteF g H x i j-liteF g H z i j‖ ≤
      touchprice H p i j *
        (fare (belle y p.B) (profile x.1) (profile z.1)/e):=by
  let T:=tagLite (b:=p.B) H
  unfold liteF touchprice; simp only [comp_apply]
  rw [T.sum,T.sum,Matrix.sum_apply,Matrix.sum_apply,←sum_sub_distrib,sum_mul]
  refine (norm_sum_le ..).trans ?_
  refine sum_le_sum fun S _=>?_
  by_cases o:T.cost S i j = 0
  · change _ ≤ T.cost S i j * _
    simpa only [← show T.cost=T.cost from rfl,o,zero_mul] using
      ((T.pass S).expo i j).variation (g.roll x) (g.roll z) -- goal simpl?
  obtain ⟨d,f⟩:=T.good _ i j o
  have h:=girder_l G _ d f
  refine (((T.pass S).expo i j).variation _ _).trans
    (mul_le_mul_of_nonneg_left ?_ ((T.pass S).nonn i j))
  change fare S (profile (U x)) (profile (U z)) / |e| ≤ _
  rw [abs_of_pos g.pos, fare_swap (pilotL g G h x t) (pilotL g G h z v)]
  exact div_le_div_of_nonneg_right (fare_inc ((halo_subset ..).trans h) _ _) g.pos.le


omit G g

lemma cup_money(h:0<a):
   ∑ i:Single N,∑ j:Single N,touchprice H p i j ≤ c:=by
 let T:=tagLite (b:=p.B) H
 apply le_trans _ (T.paid.trans_eq (one_mul c))
 simp only [touchprice,savings,saleM]
 refine sum_le_sum fun i _=>sum_le_sum fun j _=>sum_le_sum fun S _=>
   le_mul_of_one_le_left ((T.pass S).nonn i j) (rent_one (by positivity) _)

structure Matinee (p:BudgetPoint)(y:Site N)(e c:ℝ)(B:Orbit N→OP N):Prop where
  pos:0<e
  borel:Measurable B
  tint(x:Orbit N)(t:Seat N→SU.E):
    B (Lattice.gauge t x.1,threadG t x.2)=twist (tradew N t) (B x)
  fails(x:Orbit N) : ¬pingS p.threshold (hoop y p.B) x.1 → B x=0
  fees : ∃ w:Toll (Single N),
    (∑i:Single N,∑j:Single N,w i j) ≤ c ∧
    (∀ (i j:Single N),w i j≠0 → node i.1.1 ∈ belle y p.B ∧ node j.1.1 ∈ belle y p.B) ∧
    (∀x i j,‖B x i j‖ ≤ w i j) ∧
    ∀x z: Orbit N,pingS p.threshold (hoop y p.B) x.1 → pingS p.threshold (hoop y p.B) z.1 →
     ∀i j, ‖B x i j-B z i j‖ ≤
        w i j * (fare (belle y p.B) (profile x.1) (profile z.1)/e)


include G g
lemma opera : Matinee p y e c (coinF g H true):=by
 let F:=latticeFieldEstimates g G H true
 refine ⟨g.pos, ?_, ?_, ?_, touchprice H p,cup_money (p:=p) H G.apos,?_,?_,?_⟩
 · rw [show coinF g H true=(fun x=>∑S,F.wick S x) from funext F.assemble]
   exact Finset.measurable_fun_sum _ fun S _=>(F.fee S).borel
 · intro x t; rw [F.assemble,F.assemble,map_sum];exact sum_congr rfl fun S _=>(F.fee S).tint x t
 · intro x h; simp [coinF,silkcut,retina,h]
 · let T:=tagLite (b:=p.B) H
   intro i j v; change ∑S,T.cost S i j≠0 at v
   obtain ⟨S,t,o⟩:=exists_ne_zero_of_sum_ne_zero v
   obtain ⟨d,s⟩:=T.good _ i j o
   obtain ⟨_,a,b⟩:=((T.pass S).expo i j).triggered o
   exact ⟨girder_i G _ d s a,girder_i G _ d s b⟩
 · intro x i j
   rw [F.assemble,Matrix.sum_apply]
   exact (norm_sum_le ..).trans (sum_le_sum fun S _=> (F.fee S).value x i j)
 intro x z m n i j
 simpa only [coinF,silkcut,retina,m,n,if_true] using afternoon g G H x z m n i j

#print axioms opera

end YM.CF.Gingham.Ruff
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Finset Lattice Wilson Cube SU Lat Scree Skye Tulip RG Fock
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {N:Side}
def beagle (y:Site N)(p:BudgetPoint):= hoop y (p.B+2)

lemma pingCyl(M:Support (More N))(p:ℝ){U V:Pane N}
    (g: Agrees (Lattice.halo 2 M) U V):
    pingS p M U ↔ pingS p M V:=by
    have hp(i:Face (Per (More N)))(d:¬Disjoint M (touched i)): faceValue V i=faceValue U i:=by
       obtain ⟨x,a,b⟩:=Finset.not_disjoint_iff.mp d
       exact (WilsonStartup.face_local i _ _ (agrees_mono g
        (fun y v=>halo_spec.mpr ⟨x,a,DPress.Plaque.bill i b v⟩))).symm
    exact ⟨fun h i t=> (hp i t).symm ▸ h i t, fun h i t=> hp i t ▸ h i t⟩

variable {A:Orbit N→OP N}{p:BudgetPoint}{y:Site N}{e c:ℝ}
lemma innerbeagle(y:Site N)(p:BudgetPoint): Lattice.halo 2 (hoop y p.B) ⊆ beagle y p:=
  halo_spread (s:=p.B) (by
    intro i h
    simpa [halo_spec] using (show i∈Lattice.halo p.B {bouton y} from h)) (by omega)


lemma Matinee.cyl (h: Matinee p y e c A) (x z:Orbit N) (g:Agrees (beagle y p) x.1 z.1):
  A x=A z:=by
  have iff:=pingCyl (hoop y p.B) p.threshold
    (agrees_mono g (Finset.coe_subset.mpr (innerbeagle y p)))
  by_cases t: pingS p.threshold (hoop y p.B) x.1
  · obtain ⟨w,d,k,j,r⟩:=h.fees
    have f:belle y p.B⊆beagle y p:=
      (innerlude y p.B).trans ((halo_subset ..).trans (innerbeagle y p))
    ext i l
    apply sub_eq_zero.mp;apply norm_le_zero_iff.mp; apply (r x z t (iff.mp t) i l).trans
    rw [fare_cyl (agrees_mono g (Finset.coe_subset.mpr f)),zero_div,mul_zero]
  rw [h.fails x t,h.fails z (mt iff.mpr t)]

lemma Matinee.pay (h: Matinee p y e c A)(x: Orbit N): ∑ i,∑ j, ‖A x i j‖ ≤ c:=by
  obtain ⟨w,d,k,j,r⟩:= h.fees
  exact (sum_le_sum fun i (_:i∈univ)=>sum_le_sum fun _ _=>j x _ _).trans d

