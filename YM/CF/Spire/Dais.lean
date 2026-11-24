import YM.CF.Spire.City
import YM.CF.Jet.Kip
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Spire
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Scroll Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Branch Jet
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {X:Type*}(N:Side)(A:Shape)(b:Bool)
lemma polar_c(b:Bool):Continuous (polarX b):=by
 cases b; exact continuous_id; apply Topology.IsInducing.continuous_iff (g:=SU.fund) (show Topology.IsInducing SU.fund from ?_)|>.mpr; exact cc_cont.comp SU.fund_cont -- tune
 exact (SU.fund_cont.isClosedEmbedding fund_inj).isInducing
def roarD(n:Side)(e:Shape)(S:Seal (Site (More n))): Seal (Site (More n)):= S.image (e.anon n)
lemma prow : Exceed (terr (More N)) (terr (More N)) (roarD N A) 1 1:=by
 have he : ∀ x y:Site (More N),(terr _).span (A.anon N x) (A.anon N y)=(terr _).span x y:= fun x y=>by simp [terr,Shape.anon,affine]
 refine ⟨?_,fun {S} h=> ?_,?_⟩
 · intro T p; induction p with
   | single x=> unfold roarD; rw [image_singleton]; exact .single _
   | @join T x y p u q h=> rw [roarD,image_insert]; exact h.join (mem_image_of_mem _ u) (by rw [he]; exact q)
 · unfold roarD; rw [card_image_of_injective _ A.anon_b.1]; simp
 intro x; obtain ⟨v,p⟩:= A.anon_b.2 x
 refine ⟨{v},by simp,fun S h g=>⟨_,mem_singleton_self _,?_⟩⟩; unfold roarD at g; rw [←p] at g; obtain ⟨m,h,q⟩:=mem_image.mp g; rw [← A.anon_b.1 q]; exact h
variable {N}
lemma riot (i:Site (More N))(x y:Bkg (More N))(t:Step)(S:Seal (Site (More N)))(u:Agrees S x y)(l:i∈S)(p:i+t.vec∈S): t.read x i=t.read y i:=by
 have hx(v)(h:v∈visits i [t]):v∈S:=by simp [visits] at h; exact h.elim (fun h=>h ▸ l) (fun h=>h ▸ p)
 have he:= travel_local i [t] x y (fun i p c=> u i (hx _ p) (hx _ c)); simpa [travel] using he
-- Draw cost transport
lemma tutor (K:ℝ)(n:ℕ)(p:1≤K): ∃ C:ℝ,K ≤ C ∧∀ (N:Side)(A:Shape)(b:Bool)(X:Type)[NormedAddCommGroup X][NormedSpace ℝ X] (U:X→ Bkg (More N))(x:X) (f:X→ Stun N), TransK n U x K→seek f n x K→ TransK n (stir (xtra b) A ∘ U) x C ∧ seek (fume (xtra b) A ∘ f) n x C:=by
 obtain ⟨D,hD,H⟩:=factor_is (zero_le_one.trans p) n 1
 let V: Op SU.F→L[ℝ] Op SU.F:= by
    refine { toFun:=cc,map_add':=cc_add, map_smul':=fun a b=> cc_rsmul a b, cont:= cc_cont} -- tune
 let W: Vect→L[ℝ] Vect:= by
    let F:Vect→ₗ[ℝ] Vect:=⟨⟨dove true, fun a b=>by apply PiLp.ext; intro i; change star (a.ofLp i+b.ofLp i)=_; rw [star_add]; rfl⟩, fun a b=>by apply PiLp.ext; intro i; change star (a • b.ofLp i)=_; rw [star_smul,star_trivial]; rfl⟩; exact F.toContinuousLinearMap
 let a:=max K D; refine ⟨max a (max (‖V‖*D) (‖W‖*K)),(le_max_left ..).trans (le_max_left ..),fun N A b X _ _ U x f g p=> ?_⟩
 constructor
 · rintro ⟨v,i⟩; let d:=(posDir i).rotate A.s; let y:=A.anon N v; have he(t:X): SU.fund ((stir (xtra b) A ∘ U) t (v,i))=windX b (SU.fund (travel (U t) y [d])):=by
     change SU.fund ((posDir i).read (stir (xtra b) A (U t)) v)=_; rw [veil_x]; simp only [travel,mul_one]; exact polar_val b _
   have hp:= H X _ U x g y [d] (by simp); simp_rw [he]; cases b; exact hp.mono ((le_max_right ..).trans (le_max_left ..)); exact (hp.linear V le_rfl).mono ((le_max_left ..).trans (le_max_right ..)) -- tune
 intro i; cases b; exact (p (A.anon N i)).mono ((le_max_left ..).trans (le_max_left ..)); exact ((p (A.anon N i)).linear W le_rfl).mono ((le_max_right ..).trans (le_max_right ..))
variable (m B: Side)(e q:ℝ)
def ripple(x:Brace.Chord m B e q): Brace.Chord m B e q:=⟨(stir (xtra b) A x.val.1,fume (xtra b) A x.val.2), (keepC _ _ _ _ x.property.1),swayX (N:=CSide m B) _ _ _ _ _ x.property.2⟩
lemma ripple_c: Continuous (ripple A b m B e q):=by
 apply Continuous.subtype_mk
 let N:=CSide m B; have he:Continuous (stir (N:=N) (xtra b) A):=by
   refine continuous_pi fun i=>?_; let T:= Site (More N); let f:=fun x:Bkg (More N)=>Lattice.pull A.s (wrap _ (2 • A.t)) x i; change Continuous (polarX b ∘ f); unfold f
   refine (polar_c b).comp ?_; unfold Lattice.pull; unfold Step.read; split <;> fun_prop -- tune
 have ht: Continuous (fume (N:=N) (xtra b) A):= continuous_pi fun i=> (xtra b).X.continuous.comp (continuous_apply _)
 exact (he.comp (continuous_fst.comp continuous_subtype_val)).prodMk (ht.comp (continuous_snd.comp continuous_subtype_val))
lemma ripple_r(S:Broc.Table m B)(x y:Brace.Chord m B e q)(p:(pWorks m B e q).rel (roarD (CSide m B) A S) x y): (pWorks m B e q).rel S (ripple A b m B e q x) (ripple A b m B e q y):=by
 let N:=CSide m B; let Z:=A.anon N; have he(i)(h:i∈S):Z i ∈ roarD N A S:= mem_image_of_mem _ h
 constructor
 · rintro ⟨v,i⟩ a h; change (posDir i).read (stir (xtra b) A _) v=(posDir i).read (stir (xtra b) A _) v; rw [veil_x, veil_x, riot (A.anon (CSide m B) v) x.val.1 y.val.1 _ _ p.1 (he v a) (by rw [← salt]; exact he (v+(posDir i).vec) h)] -- tune
 intro i h; exact congr_arg ((xtra b).X) (p.2 _ (he _ h))
end YM.CF.Spire
