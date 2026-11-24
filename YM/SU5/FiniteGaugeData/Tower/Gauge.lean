import YM.SU5.FiniteGaugeData.Tower.Atlas
import YM.SU5.FiniteGaugeData.Tower.Reflect
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
/-!
# Covariance is a cover-test property

Preserve the physical gauge-invariant even test language in identifying
periodic and cover marks. The period data use the two simultaneous gauge
transformations (singlets with no second-link input as special case),
including on AP fields, and the consequent literal torus mark law is paid on
*all* periods (even if deriving from just one box). Only claims about the
*inputs* here (not yet showing a limit state or a block respects the gauge
symmetry).
-/
set_option maxHeartbeats 580000
open Fock Pastry Tenant
section one_particle
variable {N:Side}
lemma tradition(x:Cover)(b:SpinIdx)(g:Seat N→SU.E)(p:SU.Slot):
    acts (tradew N g).val (basisC N x b p)=∑ q:SU.Slot, (matter (g (node (wrap N x)))).val q p • basisC N x b q:=by
 let s:Site N × SpinIdx:= (wrap N x,b)
 have he:
    acts (tradew N g).val (basisKet ((s,p):Single N))=∑ q:SU.Slot,(matter (g (node (wrap N x)))).val q p • basisKet ((s,q):Single N):=by
    apply PiLp.ext; rintro ⟨l,r⟩
    rw [basis_act]
    change jump (Equiv.refl _) (fun i=> (matter (g (node i.1))).val) (l,r) (s,p)=_
    simp_rw [jump_apply,Equiv.refl_apply]
    simp_rw [WithLp.ofLp_sum,Finset.sum_apply,WithLp.ofLp_smul,Pi.smul_apply,basis_apply]
    by_cases hx:l=s
    · subst l; simp [s]  -- ite sum
    simp [hx]
 let t:= Lifted.winding N x
 unfold basisC; rw [map_smul]; change t • (acts (tradew N g).val (basisKet ((s,p):Single N)))=_
 rw [he,Finset.smul_sum]; exact sum_congr rfl fun q _=>smul_comm ..
lemma tradition_star (n:Side)(h:Seat n→SU.E): tradew n h⁻¹=star (tradew n h):=by
 change _ = _⁻¹; rw [eq_inv_iff_mul_eq_one]; rw [Hive.trade_c,inv_mul_cancel,Hive.trade_p]
end one_particle

section cover_network
variable {N:Side}(g:Cover→SU.E)(h:Seat N→SU.E)
private lemma gauge_ct:Continuous (Lattice.gauge g : LinksC→LinksC):=by
 unfold Lattice.gauge; apply continuous_pi; intro e; fun_prop
private lemma tap_locus {v v':LinksC} {S:Finset Cover}(t:Agrees S v v'):Agrees S (Lattice.gauge g v) (Lattice.gauge g v'):= by
 intro i p q; unfold Lattice.gauge; rw [t i p q]
def suits (S:Finset Cover):Prop:=∀ x∈S,g x=h (wrap (More N) x)
lemma alignment {S:Finset Cover}(v:Pane N)(t:suits g h S):Agrees S (Lattice.gauge g (onC N v)) (onC N (Lattice.gauge h v)):=by
 rintro ⟨x,i⟩ a b
 unfold Lattice.gauge; rw [onC_spec,onC_spec]; simp only; rw [t _ a,t _ b,map_add,wrap_step]
lemma suits_every {S:Finset Cover}(p:Hosp S N):∃ h:Seat N→SU.E,suits g h S:=by
 let h(i:Seat N):= if t:∃ x:S,wrap (More N) x.val=i then g (Classical.choose t).val else 1
 refine ⟨h,fun i e=>?_⟩
 have t:∃x:S,wrap (More N) x.val=wrap (More N) i:=⟨⟨i,e⟩,rfl⟩
 have he:= p.seat_ ((Classical.choose t).property) e (Classical.choose_spec t)
 unfold h; rw [dif_pos t, he]

variable {S: Finset Cover}{wide b:Bool}
private lemma colored {f:PairsC→ℂ}(p:Coeff wide S f): Coeff wide S (f ∘ Prod.map (Lattice.gauge g) (Lattice.gauge g)):=by
 refine ⟨fun v=>?_,Env.along p.env ((gauge_ct g).prodMap (gauge_ct g)).measurable,?_⟩
 · obtain ⟨u,h,h'⟩:=p.narrow v
   exact ⟨u ∘ Lattice.gauge g,h.comp (gauge_ct g),by rw [h']; rfl⟩
 intro x y a b; exact p.locus _ _ (tap_locus g a) (tap_locus g b)

variable (Λ':Calibration)
local notation "Cov"=> tradew

def cardia (S:Finset Cover)(F G:Family Λ'):Prop := ∀ (n:Side)(h:Seat (Λ'.c n)→SU.E)(x:Fields (Λ'.c n)), suits g h S→
   G n x = twist ((quantU (tradew (Λ'.c n) h))⁻¹) (F n (simultaneous h x))

lemma digest_cover {F:Family Λ'}(p:InTest Λ' wide S b F):∃ G: Family Λ', InTest Λ' wide S b G∧cardia g Λ' S F G:=by
 let Γ:= fun (n:Side)(h:Seat (Λ'.c n)→SU.E)=> twist ((quantU (tradew (Λ'.c n) h))⁻¹)
 -- relation uses inverse gauge
 induction p with
 | @seed f p=>
    refine ⟨scalar Λ' (f ∘ Prod.map (Lattice.gauge g) (Lattice.gauge g)),.seed (colored g p),?_⟩
    intro t h x y; unfold scalar; rw [twist_scalar,map_one]; exact congrArg (fun z :ℂ=> z • (1:FC (Single (Λ'.c t)))) (p.locus _ _ (alignment g h _ y) (alignment g h _ y))
 | @creator a i t p v=>
    let d:= (star (matter (g (nodeC a))).val)
    refine ⟨∑ q:SU.Slot,d q t • creation Λ' a i q,.sum _ _ (fun q _=> .smul _ (.creator q p v)),?_⟩
    intro n h x ht; let H:= tradew (Λ'.c n) h
    have hx: tradew (Λ'.c n) h⁻¹ = star H:=tradition_star (Λ'.c n) h
    simp_rw [Finset.sum_apply,Pi.smul_apply]
    unfold creation; rw [← star_coherent (tradew _ h),←tradition_star (Λ'.c n) h,twist_create,tradition,map_sum]; simp_rw [map_smul]
    unfold d; rw [node_of, ht _ v]; simp_rw [Pi.inv_apply,map_inv]; rfl
 | @remover a i t p v=>
    let d:= (star (matter (g (nodeC a))).val)
    refine ⟨∑ q:SU.Slot,star (d q t) • removal Λ' a i q,.sum _ _ (fun q _=> .smul _ (.remover q p v)),?_⟩
    intro n h x ht
    simp_rw [Finset.sum_apply, Pi.smul_apply]; unfold removal
    rw [←star_coherent (tradew _ h), ←tradition_star (Λ'.c n) h,twist_remove,tradition]; unfold Fock.remove d; rw [map_sum, star_sum,node_of, ht _ v]; simp_rw [map_smul, star_smul, Pi.inv_apply,map_inv]; rfl
 | mul _ _ r s=>
    obtain ⟨d,t,k⟩:=r; obtain ⟨e,l,u⟩:=s
    exact ⟨d*e,.mul t l,by intro n h x z; simp only [Pi.mul_apply,k n h x z,u n h x z,map_mul]⟩ -- k function?
 | add _ _ r s=> obtain ⟨d,t,k⟩:=r; obtain ⟨e,l,u⟩:=s; exact ⟨d+e,.add t l,fun n h x z=> by rw [Pi.add_apply,Pi.add_apply,k n h x z,u n h x z,Pi.add_apply,Pi.add_apply,map_add]⟩
 | smul c _ r=> obtain ⟨d,t,k⟩:=r; exact ⟨c • d,.smul _ t,fun n h x z=>by simp only [Pi.smul_apply,k n h x z,twist_scalar]⟩
 | zero=> exact ⟨0,.zero,fun _ _ _ _=> (map_zero _).symm⟩
 | one=> exact ⟨1,.one,fun _ _ _ _=> (map_one _).symm⟩
where
 star_coherent{I:Type}[Fintype I][LinearOrder I](A:UNI I) : quantU (star A)=(quantU A)⁻¹:= quantU_star A

-- hence native covariance is necessary+sufficient already on one embedding (for matching papers).
lemma complete_cov {F:Family Λ'} (p:InTest Λ' true S false F)(n:Side)(t:Hosp S (Λ'.c n))(x:covariant (F n)): ∀ t, covariant (F t):=by
 intro q s y
 let g:Cover→SU.E:=fun x=>s (wrap (More (Λ'.c q)) x)
 obtain ⟨D,v,H⟩:= digest_cover g Λ' p
 obtain ⟨f,u⟩:=suits_every g t
 have he:D n=F n:=by
    funext X; rw [H _ f _ u,x]; exact twist_inv ..
 have ht:D=F:= box_ext Λ' S v p t he
 have hv:F q y= _:= ht ▸ H q s y (fun _ _=>rfl)
 rw [hv]; symm; change twist _ (twist _ _) = _
 let U:= quantU (tradew (Λ'.c q) s)
 change twist U (twist (star U) _) = _; nth_rw 1 [← star_star U]; exact twist_inv (star U) _

lemma atlas_color (n:Side){F:Mark (Λ'.c n)} (t:Tivoli S (Λ'.c n))(p:AtSupport false (Satin.region S (Λ'.c n)) F)(v:covariant F):∀ m,covariant (extendAtlas S Λ' n t F m):=complete_cov Λ' (dictionary S Λ' n t F p) n (t.hosp) ((native S Λ' n t F p).symm ▸ v)
end cover_network
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.atlas_color
