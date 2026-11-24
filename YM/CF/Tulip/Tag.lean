import YM.CF.Tulip.Bill
set_option autoImplicit false
noncomputable section
namespace YM.CF.Tulip
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
/-- flatten colors outer for K operations -/
abbrev Single (N:Side) := (Site N × SpinIdx)×Slot
def helix (N:Side): Single N ≃ Model N:= Equiv.prodAssoc ..
abbrev Chin (N:Side):=Stem (More N)
def forum (N:Side)(e:ℝ): Stage (Site (More N)) (Single N) ↥(Openc (More N) e) (Site (More N)→E):=affair e fun i:Single N=> node i.1.1
variable {N:Side}{e:ℝ}
def tradew (N:Side)(g:Site (More N)→E): UNI (Single N):=⟨jump (Equiv.refl _) (fun i=> (matter (g (node i.1))).val),jump_unitary _ _ (fun i=>(matter _).property)⟩
def bail (N: Side)(e:ℝ): Branch.Tag (forum N e):= ⟨tradew N,fun g i j hp=> by
  have hh:i.1 ≠ j.1:=by intro h; exact hp (congr_arg node (congr_arg Prod.fst h))
  simp [tradew,jump_apply,hh]⟩
lemma meterQ (N e): Capacity (forum N e) quota:=by
  let b:=forum N e
  refine ⟨glen,fun i j=>?_,fun i j=>?_⟩
  · exact (Tenant.reach ..).trans (mul_le_mul_of_nonneg_right quota_bound (by positivity))
  let W:=board b (Branch.bay b.F i j); let S:= board (Tenant.slotK N) (bay b.F i j)
  have he : S.card=W.card:=by
    have ht : S=W.image (helix N):=by ext1 x; obtain ⟨x,rfl⟩:= (helix N).surjective x; rw [Finset.mem_image, show (∃ y ∈ W, helix N y=helix N x) ↔ x∈ W by simp]; simp only [S,W,board, Finset.mem_filter, Finset.mem_univ,true_and]; rfl
                                              -- inspect
    rw [ht,Finset.card_image_of_injective _ (Equiv.injective _)]
  rw [← he]; exact (Tenant.ample_slots N).place i j

abbrev Solo (a r:ℝ)(f:Chin N→ Op (Single N))(e:ℝ):= Crown (badge _) (bail N e) (bail N e) a r (fun x=> f x.val)
lemma axis_down (a r:ℝ){f:Chin N→Op (Single N)}(h:Solo a r f e) (d:ℝ)(hp:0<d)(hl:d≤e): Solo a r f d :=by
  let ρ(x : Openc (More N) d) : Openc (More N) e:= ⟨x.val, filt' x.val d e x.property hl⟩
  have T:Towards (forum N e) (badge _) (forum N d) (badge _) ρ 1:=by
    refine ⟨Continuous.subtype_mk continuous_subtype_val _,rfl,rfl,fun _ _=>rfl,fun S x y=>?_,fun f h V hs γ p=>?_⟩
    · rw [one_mul]; change fare S x.val y.val/|e|≤fare S x.val y.val/|d|; gcongr; exact fare_t ..; all_goals simp [abs_of_pos hp,abs_of_pos (hp.trans_le hl), hl]
    exact h V hs (ρ ∘ γ) p
  exact T.bring (s':=bail N d) (t':=bail N d) rfl rfl h le_rfl
-- antisim
lemma icy_g (x : Stem N)(g:Site N→E): ice (relayg g x)=relayg g (ice x):=by funext ⟨i,a⟩ t; cases t <;> simp [ice,relayg,mul_assoc]
lemma burnOut : Continuous (ice (N:=N)) := by unfold ice; fun_prop
lemma snowy {V:Set ℂ} (h:IsOpen V)(x:ℂ→Stem N)(hx:DifferentiableOn ℂ x V): DifferentiableOn ℂ (fun i=> ice (x (star i))) (star ⁻¹' V) :=by
  intro i g
  apply DifferentiableAt.differentiableWithinAt
  apply differentiableAt_pi.mpr
  intro j; apply differentiableAt_pi.mpr; intro k
  let f (i:ℂ):= x i j (!k)
  have hp: DifferentiableAt ℂ f (star i):=differentiableAt_pi.mp (differentiableAt_pi.mp (hx.differentiableAt (h.mem_nhds g)) j) _
  exact differentiableAt_star_conj_iff.mpr hp

def pale (A : Chin N→Op (Single N))(x):= star (A (ice x))
lemma solo_opp {A:Chin N→Op (Single N)}{a r}(H:Solo a r A e): Solo a r (pale A) e:=by
  let X:=Openc (More N) e; let f(x:X):↑X:=⟨ice x.val,ice_o x.val e x.property⟩; let b:=forum N e
  refine Crown.impose H f ?_ ?_ ?_ ?_
  · exact (burnOut.comp continuous_subtype_val).subtype_mk _
  · intro g d; exact Subtype.ext (icy_g ..)
  · intro S x y; change fare S (ice x.val) (ice y.val)/_=_; rw [ice_f]; rfl
  intro g h; exact realigns h f fun V e γ p=> snowy e (fun z=>(γ z).val) p
end YM.CF.Tulip
