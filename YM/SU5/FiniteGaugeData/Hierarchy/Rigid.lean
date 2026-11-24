import YM.SU5.FiniteGaugeData.Hierarchy.Rouge
/-! # Gauge invariant wide test algebra, CAR Fock convention. Rigidity of covariant in the period, no periodic `takes` condition needed. And gauge invariance of the multiresolution lift. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Girt Mir
namespace Tint
section
variable {K:Calibration}{S:Finset Cover}(g:Cover→SU.E){x : Family K}{b:Bool}
abbrev Realizes (S:Finset Cover){N:Side}(G:Seat N→SU.E): Prop:= ∀ i∈S,G (wrap (More N) i)= g i

private lemma floors {N:Side}(t:Seat N→SU.E)(p: Realizes g S t){W:Pane N}:
    Agrees S (gauge g (onC N W)) (onC N (gauge t W)):=by
  rintro ⟨x,i⟩ h hp; rw [onC_spec]; unfold Lattice.gauge; rw [onC_spec,p x h,←p (x+step i) hp, map_add,wrap_step]
private lemma coined {N:Side} (t:Seat N→SU.E)(p: Realizes g S t)(x:Cover)(u:nodeC x∈S)(i:SpinIdx)(b:SU.Slot):
    acts (tradew N t).val (basisC N x i b)= ∑ j:SU.Slot,(SU.matter (g (nodeC x))).val j b • basisC N x i j:= by
  have he (x:Site N×SpinIdx):
      acts (tradew N t).val (basisKet (x,b))=∑ j:SU.Slot,(matter (t (node x.1))).val j b • basisKet (x,j):=by
    apply PiLp.ext; rintro ⟨y,c⟩; rw [basis_act]; simp only [WithLp.ofLp_sum,Finset.sum_apply,basis_apply,WithLp.ofLp_smul,Pi.smul_apply, smul_eq_mul,mul_ite,mul_one,mul_zero]; rw [sum_eq_single c]; swap; · intro k _ e; rw [if_neg (fun w=>e (Prod.mk.inj w).2.symm)]
    swap; · simp
    change jump (Equiv.refl _) (fun p : Site N × SpinIdx=> (matter (t (node p.1))).val) (y,c) (x,b)=_; rw [jump_apply]; simp only [Equiv.refl_apply,Prod.mk.injEq,and_true]; split_ifs with h; · rw [h]
    rfl
  unfold basisC; rw [map_smul]; unfold Lifted.index; rw [he,smul_sum]; refine sum_congr rfl fun j _=>?_ ; simp only [node_of, p _ u]; exact smul_comm ..

/-- Conjugating the CAR frame and gauging the field arguments can each be represented in the same cover space. Only for native actions `Realizes` on the support; every sufficiently roomy torus admits it. -/
private lemma envelopeTurn (p:InTest K true S b x):
    ∃ A B:Family K, InTest K true S b A ∧ InTest K true S b B ∧
    ∀ (m:Side)(t:Seat (K.c m)→SU.E), Realizes g S t→∀ a, x m (simultaneous t a)=A m a ∧ twist (quantU (tradew (K.c m) t)) (x m a)= B m a := by
  induction p with
  | @seed f p=>
    let W(v:PairsC):= (gauge g v.1,gauge g v.2); have he(x y:LinksC)(a: Agrees S x y):Agrees S (gauge g x) (gauge g y):=fun i s e=>by unfold Lattice.gauge; rw [a i s e]
    have ht:Coeff true S (f ∘ W):= ⟨fun _=> by contradiction,Env.along p.env (by unfold W Lattice.gauge; fun_prop),fun x y q u=>p.locus (W x) (W y) (he _ _ q) (he _ _ u)⟩
    refine ⟨scalar K (f ∘ W),scalar K f,.seed ht,.seed p,fun m t v a=>?_⟩; unfold scalar; rw [twist_scalar,map_one]; refine ⟨congrArg (fun x:ℂ=>x • _) (Eq.symm ?_),rfl⟩; apply p.locus (W _) _ <;> exact floors g t v
  | @creator x i b e u=>
    let Z:= (matter (g (nodeC x))).val; refine ⟨creation K x i b,∑ j:SU.Slot,Z j b • creation K x i j,.creator b e u,InTest.sum _ _ (fun j _=>.smul _ (.creator j e u)),fun m t v a=>?_⟩
    refine ⟨rfl,?_⟩; simp_rw [creation, twist_create,coined g t v x u i b,Finset.sum_apply,map_sum,Pi.smul_apply,map_smul]; rfl
  | @remover x i b e u=>
    let Z:= (matter (g (nodeC x))).val; refine ⟨removal K x i b,∑ j:SU.Slot,star (Z j b) • removal K x i j,.remover b e u,InTest.sum _ _ (fun j _=>.smul _ (.remover j e u)),fun m t v a=>?_⟩
    refine ⟨rfl,?_⟩; simp_rw [removal,twist_remove,coined g t v x u i b,Finset.sum_apply,Pi.smul_apply,Fock.remove,map_sum,map_smul,star_sum,star_smul]; rfl
  | zero=>exact ⟨0,0,.zero,.zero,fun _ _ _ _=>⟨rfl,map_zero _⟩⟩
  | one=>exact ⟨1,1,.one,.one,fun _ _ _ _=>⟨rfl,map_one _⟩⟩
  | add _ _ a b=>
    obtain ⟨f₁,f₂,p,q,h⟩:=a
    obtain ⟨g₁,g₂,s,t,k⟩:=b
    refine ⟨f₁+g₁,f₂+g₂,p.add s,q.add t,fun m v u W=>?_⟩; simp only [Pi.add_apply,(h m v u W).1,(k m v u W).1,map_add,(h m v u W).2,(k m v u W).2,and_self]
  | mul _ _ a b=>
    obtain ⟨f₁,f₂,p,q,h⟩:=a
    obtain ⟨g₁,g₂,s,t,k⟩:=b
    refine ⟨f₁*g₁,f₂*g₂,p.mul s,q.mul t,fun m v u W=>?_⟩; simp only [Pi.mul_apply,(h m v u W).1,(k m v u W).1,map_mul,(h m v u W).2,(k m v u W).2,and_self]
  | smul c _ ih=>
    obtain ⟨f₁,f₂,p,q,h⟩:=ih; refine ⟨c • f₁,c • f₂,.smul _ p,.smul _ q,fun m v u W=>?_⟩; simp only [Pi.smul_apply,twist_scalar,(h m v u W).1,(h m v u W).2,and_self]

def Durable (K:Calibration)(F:Family K):Prop:=∀ m:Side,covariant (F m)

private lemma installs {N:Side}(p:Hosp S N): ∃ t:Seat N→SU.E, Realizes g S t:=by
  classical
  let W(i:Seat N):= if h:∃ y:↥S, wrap (More N) y.val=i then g (Classical.choose h).val else 1
  refine ⟨W,fun i t=>?_⟩; unfold W; have h:∃y:↥S,wrap (More N) y.val=wrap (More N) i:= ⟨⟨i,t⟩,rfl⟩; rw [dif_pos h]; exact congrArg g (p.seat_ (Classical.choose h).property t (Classical.choose_spec h))
lemma budgeted (p:InTest K true S false x){n:Side}(h:Hosp S (K.c n))(v:covariant (x n)): Durable K x:=by
  intro m g a
  let F:= fun y=> g (wrap (More (K.c m)) y); have he: Realizes F S g:= fun x _=>rfl
  obtain ⟨k,t,l,u,hx⟩:= envelopeTurn F p; obtain ⟨f,q⟩:=installs F h -- tune
  have H: k=t:= family_eq K S h l u (by funext x; rw [←(hx n f q x).1,← (hx n f q x).2]; exact v f x)
  rw [(hx m g he a).1,(hx m g he a).2,H]

end
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
local notation "W₀" => GridStep Λ l S
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→Family (tent Y h)→ℂ}
variable {P:Call Λ l}{J:Wicket Λ l}
variable (K:Universal Y h u v I E)(R:Rolled Y h u v J P)

-- a Closed condition on each fixed support (and on the whole hierarchy with the correct notion of resolution argument).
private def rawEval (K:Calibration) (S:Finset Cover) (i:Side)(u:Fields (K.c i)): Catalog S→ₗ[ℂ] FC (Single (K.c i)):=
 { toFun:= fun x=> composeQ K S x i u
   map_add':= fun x y=>by rw [map_add]; rfl
   map_smul':= fun c x=>by rw [map_smul]; rfl }
lemma eval_c (K:Calibration)(S:Finset Cover)(i:Side)(u: Fields (K.c i)): Continuous fun x: Catalog S=> composeQ K S x i u:= ((rawEval K S i u).mkContinuous (duration S) (fun _=> compose_price ..)).continuous
lemma hom_shut (K:Calibration)(S: Finset Cover) : IsClosed {x:Catalog S| Durable K (composeQ K S x)} := by
  rw [← isSeqClosed_iff_isClosed]; intro f t b h m g W; let X:Catalog S→ FC (Single (K.c m)):= fun x=> composeQ K S x m (simultaneous g W); let Y(x:Catalog S):= twist (quantU (tradew (K.c m) g)) (composeQ K S x m W)
  exact tendsto_nhds_unique_of_eventuallyEq ((show Continuous X from eval_c ..).continuousAt (x:=t)|>.tendsto.comp h) ((show Continuous Y from (Fock.breeze (quantU (tradew (K.c m) g))).comp (eval_c K S m W)).continuousAt (x:=t)|>.tendsto.comp h) (Eventually.of_forall fun i=> (show Durable _ _ from b i) m g W)
section
lemma sold_color {F:Family (tent Y h)} (p: InTest Kₜ true S false F) (g:Hosp S (side Y i s)): covariant (sold Y h s i F) ↔ Durable Kₜ F:=by
  let q:= terrain Y h (Y.ir i) s; have hz:covariant (sold Y h s i F) ↔ covariant (F (momentm Y i s)):= (sold_v Y h s i F).symm ▸ cg q _
  exact ⟨fun H=> budgeted p (q.symm ▸ g) (hz.mp H),fun H=> hz.mpr (H _)⟩
where cg{n m:Side}(p:n=m)(F:Mark n): covariant (show Mark m from p▸F) ↔ covariant F:= by subst m; rfl
lemma ascend_g {Z:Support (More (side Y i s))}{b:Bool}{f:Mark (side Y i s)}(p:(Y.voyage i).kick≤ k)(t:s<Y.uv k)(a: AtSupport b Z f)(r:covariant f): covariant (ingress Y s i k f):=by
  let k':= (fullness Y i k p).cap_grant; let v:= crease Y s i k p t
  exact color_preserve (apt (Y.ir i) Λ.block L₁ s) _ Λ.R.odd_side D₀ (Journey.legal Λ) Λ.J.d Chi.canonical (steps Λ.V (Y.ir i) Λ.block (Y.uv k) s) (k'.branch s t) (k'.aligned s t) ((Y.voyage i).ownership s).paid v.1 v.2 f a r (rayCost Y s i k) ((Xᵣ i k).wave s).property _ _ -- arg order?

lemma snag_durable (u:Offered Y S s i k)(x:Catalog S)(p:Durable Kₜ (composeQ Kₜ S x)):
    Durable Kₜ (composeQ Kₜ W₀ (snag Y h S s i k x)):=by
  apply (sold_color Y h W₀ (s+1) i (compose_t ..) (roomy_hosp _ u.bill.upper)).1; rw [snag_pay _ _ _ _ _ _ u,transitionQ_apply,exchanged]
  exact ascend_g Y s i k u.calendar u.age (sold_affair Y h S s i (compose_t ..)) ((sold_color Y h S s i (compose_t ..) (solvent_lower Y S s u.bill)).2 p)
include K R in
lemma preserved (x:Catalog S)(p:Durable Kₜ (composeQ Kₜ S x)): Durable Kₜ (composeQ Kₜ W₀ (P S s x)):=by
  obtain ⟨k,hp⟩:=eligible_exists Y u _ K.pick.grow_k
  exact (hom_shut Kₜ W₀).mem_of_tendsto (audition _ _ (calls Y h S s R k hp) (tendsto_const_nhds (x:=x))) ((eligible_offer Y h S s K k hp).mono fun i v=> snag_durable Y h S s _ _ v x p)
-- including inner on `Solvent` periods only
include K R in
lemma inward_g (v':Solvent Y S s i)(x:Catalog S)(p:Durable Kₜ (composeQ Kₜ S x)): Durable Kₜ (composeQ Kₜ W₀ (J S s i x)) := (hom_shut Kₜ W₀).mem_of_tendsto (audition _ _ ((R.evening S s).inner i) (tendsto_const_nhds (x:=x))) ((often_offer_inner Y h S s i K v').mono fun _ p'=> snag_durable Y h S s _ _ p' x p)
end
#print axioms ascend_g
#print axioms preserved
end Tint
end YM.CF.Buffered.Afterglow.Hierarchy
