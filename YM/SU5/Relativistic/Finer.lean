import YM.SU5.Relativistic.Waffles
import YM.SU5.Relativistic.Afield
/-! Point source fee, through field-boot (prior and marker may have different colors). Control at scale ANY chart after soft exponent. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Papyrus.Franc.Loaves
open Function Set Filter NormedSpace Fock Finset Thera MeasureTheory Metric Lattice Cube Lat Fir Onyx Rush Ember SU Scroll Skye Tulip Flare BPress.Spin.Blank
open Laurent Bloch Dial Jill Crest Crest.Shore Crest.Sleet Buffered Emu
open Lifted Pea Omelet Pannier Pannier.Chancel
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder NNReal ENNReal Kronecker
attribute [local instance] opCStarAlgebra
variable {ι:Type*} {s:ℕ→Side} {S: Finset Cover} {L:List Wine} {ε:ℝ} {a:ℕ→ℝ} (x:∀ i:ℕ,Pane (s i))
def Hitch(c S:Finset Cover)(k:Side): Finset (Seat k):= S.image (wrap (More k)) -- tune Seat
private lemma stake {W:Wine}(h: Winery false S W)(hu:Tendsto a atTop (𝓝 0)) (f:∀ i,Rightful (S.image (wrap (More (s i)))) (x i) 1 (a i)):
    Tendsto (fun i=> W.fees (onC (s i) (x i))) atTop (𝓝 (W.fees 1)):=by
 classical
 let Q(p:Edge Cover):Prop:= p.1∈S ∧ p.1+step p.2 ∈ S
 let F(i:ℕ):LinksC:=fun p=> if Q p then onC (s i) (x i) p else 1
 have he(i):W.fees (F i)=W.fees (onC (s i) (x i)):= h.near _ _ (fun k x y=>if_pos (And.intro x y)) -- term inference
 have ht:Tendsto F atTop (𝓝 1):= tendsto_pi_nhds.mpr fun k=>by
    by_cases w: Q k
    · have hg:Injective brand:=fun i j p=> group.mat_injective (show fund i=fund j from congrArg Prod.snd p)
      apply (Dial.spinD.isClosedEmbedding hg).isEmbedding.tendsto_nhds_iff.mpr
      rw [tendsto_iff_norm_sub_tendsto_zero]; apply squeeze_zero (fun _=>norm_nonneg _) _ hu
      intro i; unfold F comp; simp only; rw [if_pos w,onC_spec]; let K:= wrap (More (s i)); let V:=K k.1; let W:= S.image K; have hl : (K k.1,k.2)∈ Tenant.leaks W:=by
         exact Finset.mem_filter.mpr ⟨mem_univ _, mem_image_of_mem K w.1,(by rw [← wrap_step, ←map_add]; exact mem_image_of_mem K w.2)⟩
      exact (riotPort ..).1 (f i) _ hl
    unfold F; simp_rw [if_neg w]; exact tendsto_const_nhds
 exact ((h.price.tendsto _).comp ht).congr he
variable {K:ℕ}{d:ℝ}(u:0≤d)(f:∀ ε>(0:ℝ),∃ γ> (0:ℝ),∃ w:ℕ,∀ n:Side,K ≤ n.val→ Winter 4 d n γ w ε)
include u f
abbrev terrace(N:Side)(S:Finset Cover):= S.image (wrap (More N))
private lemma floorQ (A:Staff) {i j:Bite}(v:nodeC i.root∈ S)(w:nodeC j.root∈ S)(ε:ℝ)(p:0<ε):∃ γ>(0:ℝ),∃ s:ℕ,∀ n:Side,K ≤ n.val→∀ M:Jill.Male, IsStarProjection (spar 4 M (1:Pane n))→ ∀ U:Pane n,Guard U d → Rightful (Lattice.halo s (terrace n S)) U 1 γ→IsStarProjection (spar 4 M U)→∀ a:Ket (Single n),‖a‖≤1→ ‖inner ℂ a (acts (A.stem (tickA n) (spar 4 M U)-A.stem (tickA n) (spar 4 M (1:Pane n))) (j.loc n))‖≤ε:=by
 obtain ⟨k,h,t,v'⟩:= Staff.playsA 4 d u f A ε p; refine ⟨k,h,t,fun n e M Q U k a p x z=>?_⟩; apply (norm_inner_le_norm ..).trans; apply (mul_le_of_le_one_left (norm_nonneg _) z).trans
 rw [←Bite.pace n j w,←act_mul]; apply (Flare.opy ..).trans; refine (mul_le_of_le_one_right (norm_nonneg _) (Bite.normP n j).le).trans ((v' e M (terrace n S) Q).2 U k a p)
-- uniform convergence of true P matrix at nearby gauge. coefficients. Need cost at SAME M but n maybe. Use sequences contradiction for fixed A. compare complex vacuum scalars via Lipschitz without convergence to constant by subseq. Support allows warm→0 for any given path engaged. Cheaper direct choose multipower argument algebra continue. define local test vectors permit. finite each.
omit u f
open Staff
variable {N:ℕ→Side}{M:ℕ→Jill.Male} (U V:∀ i,Pane (N i))(T:ℕ)(t:S.Nonempty)(p:∀ i,Guard (U i) d)
variable (g:Tendsto (fun i=>(N i).val) atTop atTop)(k:Tendsto (fun i=>(M i).val.val) atTop atTop)(n:∀ i, Even (N i).val)(m:∀ i,K≤ (N i).val)(q:∀ i,IsStarProjection (spar 4 (M i) (U i))) (h:∀ i,IsStarProjection (spar 4 (M i) (1:Pane (N i)))) (ε':Tendsto a atTop (𝓝 0))(z:∀ i, Rightful (Lattice.halo i (terrace (N i) S)) (U i) 1 (a i))
include g k n m q h z t u f p ε'
private lemma favo (i j:Bite)(W:Staff): let B(k):= tickA (N k); Tendsto (fun k=>inner ℂ (i.loc (N k)) (acts (W.stem (B k) (spar 4 (M k) (U k))) (j.loc (N k)))) atTop (𝓝 (agt i j W)):=by
 intro B
 let A(x:ℕ)(P:Op (Single (N x))):=inner ℂ (i.loc (N x)) (acts P (j.loc (N x)))
 let H(x:ℕ):=W.stem (B x) (spar 4 (M x) (1:Pane (N x))); let Q(x:ℕ):=W.stem (B x) (spar 4 (M x) (U x))
 have he:Tendsto (fun x:ℕ=> A x (H x)) atTop (𝓝 (agt i j W)):= supplier _ _ _ _ _ _ g k n W h
 have ht:Tendsto (fun x=>A x (Q x-H x)) atTop (𝓝 0):=by
    apply Metric.tendsto_nhds.mpr; intro e h'; obtain ⟨b,y,l,w⟩:=floorQ u f W (i:=i) (j:=j) (S:={nodeC i.root,nodeC j.root}) (by simp) (by simp) (e/2) (half_pos h')
    obtain ⟨o,hO⟩:=t; let Y:Finset Cover:={nodeC i.root,nodeC j.root}; obtain ⟨c,hf⟩:= Pannier.Chancel.ScreeV.long_cost Y o
    filter_upwards [ε'.eventually (ge_mem_nhds y),eventually_ge_atTop (c+l)] with x hx hc
    rw [dist_zero_right]; apply lt_of_le_of_lt _ (half_lt_self h')
    apply w (N x) (m x) (M x) (h x) _ (p x) _ (q x) _ (i.normP _).le
    apply Staff.rightfulInv (z x) _ hx
    have ht: terrace (N x) Y ⊆ Lattice.halo c (terrace (N x) S):=by intro i q; obtain ⟨j,p,rfl⟩:= Finset.mem_image.mp q; exact Lattice.halo_spec.mpr ⟨_,Finset.mem_image_of_mem _ hO,hf _ j p⟩
    exact Finset.Subset.trans (crease (by rfl) ht) (Finset.Subset.trans (hollowG _) (crease hc (by rfl))) -- tune L := _
 have hz:=ht.add he; rw [zero_add] at hz; refine hz.congr fun i=>?_; unfold A; rw [act_sub,inner_sub_right,sub_add_cancel]
private lemma edu (i j:Bite) : Tendsto (fun k=>tooth (spar 4 (M k) (U k)) (stilt T (spar 4 (M k) (U k)) i) (stilt T (spar 4 (M k) (U k)) j)) atTop (𝓝 (billJ T i j)):=by
 have he (s i j) := favo u f U t p g k n m q h ε' z i j s -- tune order
 let c:= Loaves.colors T i.hand; let b:=Loaves.colors T j.hand
 have ht(x y:Bite)(l p:Staff)(o:ℕ)(G:Staff): let P:= (spar 4 (M o) (U o)); let B:=tickA (N o); let X':=acts (l.stem B P) (x.loc _);let Y':=acts (p.stem B P) (y.loc _); inner ℂ X' (acts (G.stem B P) Y')=inner ℂ (x.loc _) (acts ((l.flip.mul (G.mul p)).stem B P) (y.loc _)):=by
    intro P B X' Y'; have hh:IsStarProjection B:=by unfold B; rw [←t_comp]; exact cutM_idp _
    unfold X' Y'; simp only [Staff.stem]; rw [flip_p _ _ _ (q o) hh,act_mul,act_mul,← act_inner (star _),star_star] -- tune
 unfold billJ tooth; simp only [show ∀ i k,(stilt T (spar 4 (M k) (U k)) i).1=i.hand from fun _ _=>rfl]; split_ifs
 · -- tune
   exact tendsto_const_nhds
 · let Y:=Staff.one.add (.neg .pay); refine (he (c.flip.mul (Y.mul b)) i j).congr fun x=>Eq.symm ?_; let B:=tickA (N x); have hx:= ht i j c b x Y; change inner ℂ (acts (c.stem B (spar 4 (M x) (U x))) _) (acts (1 + -(spar 4 (M x) (U x))) _)=_ at hx; rw [←sub_eq_add_neg] at hx; exact hx
 exact (he (b.flip.mul (.mul .pay c)) j i).congr fun x=>(ht j i b c x .pay).symm
private def radiant (T:ℕ)(L:List Wine):ℂ:=(L.map fun w=> w.fees 1*billW w.song T).sum
private lemma winterV (L:List Wine) (D:AreaW false S L) (v:∀ i,Rightful (terrace (N i) S) (V i) 1 (a i))(R:∀ i,Wave (Single (N i)))(b:∀ i,Sea (spar 4 (M i) (U i)) (R i)) : Tendsto (fun i=> inner ℂ (R i) (acts (tickTea (Straw (spar 4 (M i) (U i)) T) (onC (N i) (V i)) L) (R i))) atTop (𝓝 (radiant T L)):=by
 induction L with|nil=> simpa [tickTea,radiant] using tendsto_const_nhds (x:= (0:ℂ)) (f:=(atTop:Filter ℕ))|cons j L ih=>
    let F(i:ℕ):=runes (fun x y=>tooth (spar 4 (M i) (U i)) (stilt T (spar 4 (M i) (U i)) x) (stilt T (spar 4 (M i) (U i)) y)) j.song
    have hf:Tendsto F atTop (𝓝 (billW j.song T)):=offer_v _ _ (edu u f U T t p g k n m q h ε' z) _
    let Z(i:ℕ):=j.fees (onC (N i) (V i)); have hz:Tendsto Z atTop (𝓝 (j.fees 1)):=stake V (D j List.mem_cons_self) ε' v
    apply Tendsto.congr _ ((hz.mul hf).add (ih (fun i t=>D _ (List.mem_cons_of_mem _ t))))
    intro i; change Z i*F i+ _= inner _ _ _; unfold tickTea; rw [List.map_cons,List.sum_cons,act_add,inner_add_right,act_smul,inner_smul_right]; congr 1; rw [show (fun j:Bite=> creed j.hand (Straw _ _ j)) = ton ∘ (stilt T (spar 4 (M i) (U i))) from rfl, choral (q i) _ _ (b i)] -- tune
omit g k n m q h z t u f p ε'
private lemma radiates(X:List Wine): Tendsto (fun k=>radiant k X) atTop (𝓝 (tallyW X)):=by
 induction X with| nil=> exact tendsto_const_nhds (x:=0)| cons i l ih=> exact (((show Tendsto (billW i.song) atTop _ from (toes i.song).choose_spec).const_mul _).add ih)
include u f t
open Pannier.Chancel
lemma remiss (uK:0<ε)(H:AreaW false S L):∀ᶠ T:ℕ in atTop, ∃ γ>(0:ℝ), ∃ w Z:ℕ, ∀ n:Side, K≤ n.val→Z≤n.val→Even n.val→∀ M:Tulip.Male,Z ≤ M.val.val→IsStarProjection (spar 4 M (1:Pane n))→∀ P V:Pane n,Guard P d → Rightful (Lattice.halo w (terrace n S)) P 1 γ→ Rightful (terrace n S) V 1 γ → IsStarProjection (spar 4 M P) →∀ v:Wave (Single n), Sea (spar 4 M P) v→ ‖inner ℂ v (acts (tickTea (Straw (spar 4 M P) T) (onC n V) L) v)-tallyW L‖≤ ε:=by
 let b(x:ℕ):=((x:ℝ)+1)⁻¹; have hb(x):0<b x:=by unfold b; positivity
 filter_upwards [Metric.tendsto_nhds.mp (radiates L) (ε/2) (half_pos uK)] with T y
 by_contra! g
 choose N v v1 v2 M q h P V w w1 w2 t' z h' hX using fun i:ℕ=>g (b i) (hb _) i i
 have hs:Tendsto b atTop (𝓝 0):= tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
 have he:= winterV u f P V T t w (tendsto_atTop_mono v1 tendsto_id) (tendsto_atTop_mono q tendsto_id) v2 v t' h hs w1 L H w2 z h'
 have hz:= ge_of_tendsto' ((he.sub_const (tallyW L)).norm) (fun i=> (hX i).le)
 rw [dist_eq_norm] at y; linarith
end YM.CF.Papyrus.Franc.Loaves
