import YM.SU5.Relativistic.Marat
import YM.SU5.Relativistic.Berm
import YM.SU5.Relativistic.Sval
/-! # Concretion with caloric flags. Exact direct fields. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 590000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Papyrus.Franc.Meshy
open Function Filter NormedSpace Metric Fock Finset Thera MeasureTheory Lattice Cube Lat Fir Rush SU Scroll Skye Tulip Flare BPress.Spin.Blank
open Laurent Bloch Dial Jill Crest Crest.Shore Crest.Sleet Buffered
open Lifted Pea Omelet Afterglow Satin Pannier Pannier.Chancel Pannier.Chancel.ScreeV Cliplet RG Tenant Scree Loaves
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder NNReal ENNReal Kronecker
attribute [local instance] opCStarAlgebra
variable {S T: Finset Cover}{N:Side}{M:Tulip.Male}{k w v:ℕ}{s t C B η μ:ℝ}
local notation "B❀"=> Cliplet N 1
structure Crisp (M:Tulip.Male)(k w v:ℕ)(s t η μ C B:ℝ)(A:Cliplet N 1): Prop where
 atH: AtSupport false A.broad A.frame
 peg: A.birth 0∈ A.broad
 raw (x : Fields N): BlankT C B (A.frame x)
 casts(x:Fields N) (p:Guard x.2 s) (h:A.feel t v x.1) (q:Agrees (Lattice.halo w A.broad) x.2 x.1) : let V:=spar 4 M x.2; ∀ Q:IsStarProjection V,Nought (Saber (B:=tickA N) Q k) (A.frame x) V η μ (modesIn N A.broad)
-- when remiss σ>d'. read formula validated forge.True.
def Muster (s:ℝ) (N:Side)(M:Tulip.Male):Prop:= ∀ U:Pane N,Guard U s → IsStarProjection (spar 4 M U) ∧∀ (i:Axis)(a:ℤ),Guard (fling i a N U) s∧ twist (carR i a N) (spar 4 M (fling i a N U))=1-spar 4 M U
lemma vanguard : ∃ d> (0:ℝ),∃ n:ℕ,∀ d',0≤d' → d' ≤ d →∀ N:Side,n≤N.val→ ∀ M:Tulip.Male,Muster d' N M:=by
 obtain ⟨e,h,u,v⟩:= Scroll.radiance 4 (by decide); obtain ⟨w,z,l,f⟩:= Tulip.funde_q 4 (by decide); refine ⟨min e w,lt_min h z,u+l,fun d x hd N p M U g=>⟨f M _ (by omega) U (g.shrink (hd.trans (min_le_right ..))),?_⟩⟩; intro i a; let V:=fling i a N U
 have h':Guard V d:= Scroll.keepC inert (plane i a) U d g -- tune
 refine ⟨h',?_⟩; have he:=funde_f (Buffered.plane i a) inert (Window.pinLift i) (mirrorX i) V 4 (by decide) M e (v N (by omega)) (h'.shrink (hd.trans (min_le_left ..)))
 rw [show stir inert (plane i a) V=U from fling_invol i a U] at he; exact he
structure Battalion (M:Tulip.Male)(k w v:ℕ)(s t η μ C B:ℝ)(L:List (Cliplet N 1)):Prop where
 granted:∀ i∈L, Crisp M k w v s t η μ C B i
 lock : L.Pairwise (fun a b=> Disjoint a.broad b.broad)
variable {A:Cliplet N 1} {L:List (Cliplet N 1)}
lemma Crisp.blossom(h:Crisp M k w v s t η μ C B A)(f:Muster s N M)(i:Axis)(r:ℤ): Crisp M k w v s t η μ C B (A.mirror i r):=by
 constructor
 · exact h.atH.refl i r
 · exact Finset.mem_image_of_mem _ h.peg
 · intro x; let G:=reflFields i r x; exact (h.raw G).thetaF (carR i r N) ((h.atH.allV G).sector)
 intro x p t₀ u V q
 let G:=reflFields i r x; let T:= (plane i r).anon N
 have ht:A.feel t v G.1:=by
    unfold feel; apply (Finset.disjoint_image (show Function.Injective T from (show Involutive _ from fling_there (n:=N) i r).injective)).1; change Disjoint (hyphen i r (Lattice.halo v A.broad)) (hyphen i r (flags t (fling i r N x.1))); rw [coal_flags,coal_halo]; exact t₀
 have hg:Agrees (Lattice.halo w A.broad) G.2 G.1:= fling_local (n:=N) i r (Lattice.halo w A.broad) (x:=x.2) (y:=x.1) (by rw [show (Lattice.halo w A.broad).image _= _ from coal_halo i r A.broad w]; exact u) -- tune
 obtain ⟨v0,b⟩:=(f x.2 p).2 i r; let Q:= (f G.2 v0).1; exact Nought.race Q q (Cascade.plus_P N) (refl_modes ..) b (by rw [Spire.touchP]; exact flatTset i r) (h.casts G v0 ht hg Q) ((h.atH.allV G).sector)
local notation "©" => Battalion M k w v s t η μ C B
namespace Battalion
variable (h:Battalion M k w v s t η μ C B L)
lemma alone(p:Crisp M k w v s t η μ C B A): © [A]:= ⟨fun i h=>List.mem_singleton.mp h ▸ p,by simp⟩
include h
lemma cloud(i:Axis)(r:ℤ)(p:Muster s N M): © (L.map (fun a=> a.mirror i r)):=by
 constructor
 · intro i k; obtain ⟨a,b,rfl⟩:=List.mem_map.mp k; exact (h.granted a b).blossom p _ _
 apply List.pairwise_map.mpr; exact h.lock.imp (fun {a b} h=> (Finset.disjoint_image ((show Involutive _ from fling_there (n:=N) i r).injective)).2 h)
lemma tack (U:List (Cliplet N 1))(q:© U)(e:Disjoint (whereV L) (whereV U)) : © (L++U):= ⟨fun a u=>(List.mem_append.mp u).elim (h.granted _) (q.granted _),List.pairwise_append.mpr ⟨h.lock,q.lock,fun i u a v=> e.mono (where_ge _ u) (where_ge _ v)⟩⟩
lemma permit {D:Finset (Seat N)}(p:whereV L⊆ D): AtSupport false D (probe L):=by
 induction L with
 | nil=>exact AtSupport.oneM D
 | cons A L ih=>
    let W:=(h.granted _ (List.mem_cons_self)).atH; change A.broad∪whereV L ⊆ D at p
    rw [probe_cons]; exact (W.mono (Finset.Subset.trans subset_union_left p)).mulM (ih ⟨fun B g=>h.granted B (List.mem_cons_of_mem _ g),(List.pairwise_cons.mp h.lock).2⟩ (Finset.Subset.trans subset_union_right p))
lemma shorter {X:List (Cliplet N 1)}(p:X.Sublist L) : © X:= ⟨fun i h'=>h.granted i (p.mem h'),List.Pairwise.sublist p h.lock⟩
omit h in
private lemma seek {Z:Finset (Seat N)} (h:© L)(p:∀ a∈L, ∃ i∈ a.broad,i∈ Z) : L.length≤ Z.card:=by
 induction L generalizing Z with
 | nil=> simp
 | cons a L ih=>
    obtain ⟨x,q,g⟩:= p _ List.mem_cons_self
    have ht:L.length≤ (Z.erase x).card:=by
      apply ih (h.shorter (by simp)); intro i u; obtain ⟨y,t,v⟩:= p i (List.mem_cons_of_mem _ u); refine ⟨_,t,mem_erase.mpr ⟨fun k=> ?_,v⟩⟩; exact disjoint_left.mp ((List.pairwise_cons.mp h.lock).1 i u) q (k ▸ t) -- nested eq
    rw [Finset.card_erase_of_mem g] at ht; rw [List.length_cons]; have ho:= Finset.card_pos.mpr (show Z.Nonempty from ⟨x,g⟩); omega
lemma pcount : L.length≤ (More N).val^4:=by
 exact le_trans (seek (Z:=univ) h (fun i p=>⟨_,(h.granted i p).peg,mem_univ _⟩)) (le_of_eq (by rw [card_univ,site_card]))
open Py.Rate.Pannier
lemma dirty (U:Pane N) : let H:=L.filter (fun A=> @decide _ (Classical.propDecidable (¬ A.feel t v U))); H.length≤ (roughness t U).card * (4*(v+v+1)^4):=by
 classical
 intro H; have ht:H.Sublist L:= List.filter_sublist
 apply (seek (Z:=Lattice.halo v (flags t U)) (h.shorter ht) ?_).trans ((Corona.halo_size ..).trans ((Nat.mul_le_mul_right _ (flag_coat U t)).trans_eq (Nat.mul_assoc ..)))
 intro a u; have ht: ¬ a.feel t v U:=@of_decide_eq_true (¬ a.feel t v U) (Classical.propDecidable _) (List.mem_filter.mp u).2
 obtain ⟨i,h,t'⟩:= Finset.not_disjoint_iff.mp ht; obtain ⟨w,q,l⟩:= halo_spec.mp h; exact ⟨w,q,halo_spec.mpr ⟨i,t',(separation_comm ..).trans_le l⟩⟩
lemma actual (u:0<C)(v:2≤B)(x:Fields N) : ‖probe L x‖≤ C^L.length:=by
 induction L with| nil=> simp| cons a l ih=>
    rw [probe_cons,Pi.mul_apply]; rw [List.length_cons, pow_succ']; apply (norm_mul_le ..).trans; apply mul_le_mul _ (ih (h.shorter (by simp))) (norm_nonneg _) u.le
    let K:= slept (Single N); have hv:= (h.granted _ List.mem_cons_self).raw x K.mint (show Franc.Price K.mint _ from ⟨K.signed.1.trans v,K.signed.2.trans v⟩); rw [← K.vending,show K.hat=1 from slept_b.1,show K.tagH=1 from slept_b.2.1,one_mul,mul_one] at hv; exact hv
end Battalion
end YM.CF.Papyrus.Franc.Meshy
