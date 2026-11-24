import YM.SU5.FiniteGaugeData.Pannier.Emperor
import YM.SU5.FiniteGaugeData.Pannier.Fragile
/-!
# Sheet for a good subflight.
Registers exact *interacting* filled subwaves on the repaired gauge and
sparse requested points via Tilt, at all Male. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Cliplet RG Brace
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {n:Side} {j k d w t:ℕ} {M:Tulip.Male}
namespace Cliplet
variable (L:List (Cliplet n k))
abbrev Actor:= {v// v∈L}
abbrev berries (L:List (Cliplet n k)):= Actor L × Fin k
variable {ε γ δ τ E' R:ℝ}{L}
variable (h:Flight j M w d t γ τ L)
include h
private lemma garment (U:Actor L→Seat n→SU.E): ∃ G:Seat n→SU.E,∀ A:Actor L,∀ x∈ A.val.broad,G x=U A x:=by
 classical
 let f(X):=if h:∃ i:Actor L, X∈ i.val.broad then U h.choose X else 1
 refine ⟨f,fun i x h'=>?_⟩; unfold f; let X:=(show ∃i:Actor L,x∈i.val.broad from ⟨_,h'⟩); rw [dif_pos X]; apply congrArg (fun i => U i x);
 by_contra u; exact disjoint_left.mp (h.distinct X.choose.property i.property (fun p=>u (Subtype.ext p))) X.choose_spec h'
private lemma mustInterpret {A B:Pane n}{f:Actor L→ Seat n→SU.E}{G:Seat n→SU.E} (X:∀ a:Actor L, Agrees a.val.broad A B) (u:∀ a:Actor L,∀ x∈ a.val.broad,G x=f a x)(t':∀ a:Actor L, Rightful a.val.broad (Lattice.gauge (f a) B) 1 γ): Rightful (Lattice.halo w (Stripes L)) (Lattice.gauge G A) 1 γ:=by
 apply (riotPort ..).2; rintro ⟨x,i⟩ hi
 obtain ⟨k,v,hk⟩:= halo_spec.mp (mem_filter.mp hi).2.1
 obtain ⟨a,t₀,v⟩:= (stripes_at ..).1 v; have hp: x∈ a.broad:=(h.granted _ t₀).lamp (halo_spec.mpr ⟨k,v,hk.trans (by omega)⟩)
 have hg:x+step i∈ a.broad:= (h.granted _ t₀).lamp (halo_spec.mpr ⟨k,v,(separation_triangle _ x _).trans (by have u:= Work.E01.sep_step_le x i; change separation k x ≤ w at hk; omega)⟩)
 let q:Actor L:= ⟨a,t₀⟩; have ht:Lattice.gauge G A (x,i) = Lattice.gauge (f q) B (x,i):=by simp only [Lattice.gauge]; rw [u q _ hp,u q _ hg,X q (x,i) hp hg]
 rw [ht]; exact (riotPort ..).1 (t' q) (x,i) (mem_filter.mpr ⟨mem_univ _,hp,hg⟩)
def requestBirth (i:berries L) := i.1.val.birth i.2
private lemma nobody : Injective (requestBirth (L:=L)) := by
 rintro ⟨i,a⟩ ⟨l,c⟩ p; by_cases g:i.val=l.val; · have e:i=l:=Subtype.ext g; subst i; exact congrArg _ ((h.granted l.val l.property).firm p)
 have he:=h.distinct i.property l.property g
 let x:=i.val.birth a; have hp:x=l.val.birth c:=p
 apply (disjoint_left.mp he (show x∈i.val.broad from ?_) ?_).elim; exact (h.granted _ i.property).enter (mem_image_of_mem _ (mem_univ _)); -- type?
 rw [hp]; exact (h.granted _ l.property).enter (mem_image_of_mem _ (mem_univ _))
omit h in
private lemma far_caps {S T:Finset (Seat n)}{x:Ket (Single n)}(p:withinM (modesIn n S) x) (d:Disjoint S T): withinM (modesIn n T)ᶜ x:=by
 apply within_more p; intro k h; simp only [modes_at,mem_compl] at *; exact disjoint_left.mp d h
private lemma apartBirth {i l:berries L} (p:i ≠ l){x y: Ket (Single n)}(g:i.1.val.cargo i.2 x)(u:l.1.val.cargo l.2 y): inner ℂ x y=0:=by
 have h':withinM (modesIn n {requestBirth i})ᶜ y:= far_caps u (by rw [disjoint_singleton]; exact Ne.symm (fun e=>p (nobody h e))) -- align
 let C:= cutM (modesIn n {requestBirth i}); have hp: acts C x=x:=g; have he:acts C y=0:=within_compl.mp h'
 nth_rw 1 [← hp]; nth_rw 1 [← show star C=C from (cutM_idp _).isSelfAdjoint]; rw [act_inner,he,inner_zero_right]

variable {Ξ:ℝ}{X:Fields n}{b:Bool}
private lemma summerRay {δ0:ℝ}(p: Sparkle n δ0 M j)(g:Winter j δ n γ w ε)(u:δ0≤δ)(z:Guard X.2 δ0)(v:0≤δ)(k₁:∀ (S:Finset (Seat n)), Sparse d S → HearthB R (sp b j M (1:Pane n)) S)(E : ε*R≤1/3)(κ:ε*(2*R+4*R*R)≤Ξ^3) (clean:∀ a∈ L,a.feel τ t X.1)(move:∀ a∈L,Agrees a.broad X.2 X.1)(x':∀ a∈L,a.rev=b)
    (T:Finset (Seat n))(hx:Disjoint T (whereV L)) (C:FC (Single n))(J: Fine (Tset n) (modesIn n T) false C) :
    ∃ x y z: berries L → Ket (Single n), Sheet (Tset n) (modesIn n T) (spar j M X.2) C b x y z (2*R) Ξ ∧ ∀ i:Actor L,i.val.frame X=xpert fun a=> handy b (Tset n) (x (i,a)) (z (i,a)):=by
 classical
 let A(a:Actor L) := a.val
 let α(a:Actor L):= (h.granted a.val a.property)
 choose V Y Z u' e fg a xg gY using (fun i:Actor L=> (h.granted _ i.property).peak X); obtain ⟨G,H⟩:=garment h V
 simp_rw [x' _ (Subtype.property _)] at e a gY -- tune
 let U:=Lattice.gauge G X.2; let P : Op (Single n):= sp b j M X.2; let F:Op (Single n):= sp b j M U; let K:= Stripes L; let W:=tradew n G; let C':=acts W.val;
 have hF:IsStarProjection F:= raft b (p.projection _ (z.cov G)); have ht:twist W P=F:=by unfold F P W sp; rw [handAgainst (tradew n G),show U=Lattice.gauge _ X.2 from rfl,← p.covary X.2 G z]
 have hl(i:Actor L): (A i).s ⊆ K:= stripes_ge L i.property
 have hp:Rightful (Lattice.halo w K) U 1 γ:= mustInterpret h (fun i=>move _ i.property) H fun i=> u' i (clean _ i.property); have hu:HearthB (2*R) F K := hearthB_stands (k₁ K h.sparse) (hearthB_wind g v ((z.cov G).shrink u) hp) E
 let P':= sp b j M (1:Pane n)
 let M'(S:Finset (Seat n)):= modesIn n S
 let x(i:berries L):= Y i.1 i.2; let Z'(i:berries L):=Z i.1 i.2; let x''(i:berries L):= C' (x i); let F'(i:berries L):= warmth F (M' K) (x'' i)
 let y(i:berries L) := acts (star W.val) (F' i); have hθ i: C' (y i)=F' i:=act_starUnit W _
 have cargo(i:berries L): withinM (M' (A i.1).s) (x i):=i.1.val.cargo_le (fg ..) -- tune implicit i
 have hx'(i:berries L): withinM (M' K) (x'' i):= within_more (coverSense.mpr (cargo i)) (modes_monotone (hl i.1))
 have hZ(i:berries L):withinM (M' (A i.1).broad) (Z' i):= coverSense (t:=V i.1) |>.1 ((gY i.1 i.2).symm ▸ covers_spark) -- rw tune
 refine ⟨x,y,Z', ⟨?_,?_,?_,?_,fun i=>a _ _,fun i=>(xg ..).le,?_,?_,J⟩,e⟩ -- e defeq
 · intro i; apply trim_return ht; change trim F (C' (y i)); rw [hθ]; exact server_sh hF _
 · intro i; rw [← act_unit_norm W (y i)]; change ‖C' (y i)‖ ≤_; rw [hθ]; exact warm_cost _ hF hu.2 ((act_unit_norm W (x i)).le.trans (xg i.1 i.2).le)
 · intro i; exact far_caps (within_more (hZ i) (modes_monotone (where_ge L i.1.property))) hx.symm
 · intro i; let Pn:=A i.1; rw [←act_unit_norm W (Z' i-y i)]; change ‖C' (_-_)‖≤ _; rw [map_sub,hθ,show C' (Z' i)= sparkUp P' (modesIn n Pn.s) (modesIn n Pn.broad) (x'' i) from ?_]; swap
   · change acts (tradew n G).val _=sparkUp _ _ _ (acts (tradew n G).val _); rw [agreePick Pn.broad (V i.1) G (fun v u=>Eq.symm (H i.1 v u)) (hZ i),agreePick Pn.broad (V i.1) G (fun v u=>Eq.symm (H i.1 v u)) (within_more (cargo i) (modes_monotone (h.granted _ i.1.property).enter))]; exact gY ..
   let hq:=h.granted Pn i.1.property
   have he: ‖x'' i‖ ≤1:= (act_unit_norm W (x i)).le.trans (xg i.1 i.2).le
   exact (parcel_spark g v ((z.cov G).shrink u) hp (k₁ K h.sparse) (k₁ Pn.s hq.far) (hl i.1) (fun x t y e=> (Distant.symm (h.Corset i.1.property) x t y e).trans' (Nat.le_add_right ..)) (fun x t y e=> (Distant.symm hq.halo_sp x t y e).trans' (Nat.le_add_right ..)) E hF (coverSense.mpr (cargo i)) he).trans κ
 · intro i; have hh:‖x'' i‖=1:= (act_unit_norm W (x i)).trans (xg ..); rw [← act_unit_inner W]; change inner ℂ (C' (y i)) (x'' i)=_; rw [hθ]; unfold F'; rw [warmed_contact hu.1 (hx' i) (hx' i),inner_self_eq_norm_sq_to_K,hh]; norm_num
 intro i j u; rw [← act_unit_inner W]; change inner ℂ (C' (y i)) (x'' j)=0; rw [hθ]; unfold F'; rw [warmed_contact hu.1 (hx' i) (hx' j)]; exact (act_unit_inner W (x i) (x j)).trans (apartBirth h u (fg ..) (fg ..))
omit h
private def fir (L:List (Cliplet n k)):List (berries L):= L.attach ×ˢ (List.ofFn id)
private lemma packsProd (f:berries L→FC (Single n)) (X:Fields n)(p:∀ i:Actor L,i.val.frame X=xpert fun a=> f (i,a)): probe L X=( (fir L).map f).prod:=by
 rw [probe_at]; generalize hx: L.attach =W at * -- affects fir
 rw [show fir L=W ×ˢ List.ofFn (@id (Fin k)) from ?_]; swap; · unfold fir; rw [hx] -- both lists
 have ht:W.map Subtype.val=L:= hx ▸ List.attach_map_subtype_val _
 conv_lhs=>arg 1; rhs; rw [←ht] -- unfold check; easier rewrite occ using calc
 rw [List.map_map]; clear hx ht
 induction W with
 | nil=> rfl
 | cons a L ih=> rw [List.product_cons,List.map_append,List.prod_append, List.map_cons, List.prod_cons,ih,List.map_map,List.map_ofFn]; exact congrArg (· * _) (p a)

include h
open Damask
lemma dropping {δ0:ℝ}(p: Sparkle n δ0 M j)(g:Winter j δ n γ w ε)(u:δ0≤δ)(z:Guard X.2 δ0)(v:0≤δ)(k₁:∀ (S:Finset (Seat n)), Sparse d S → HearthB R (sp b j M (1:Pane n)) S)(E : ε*R≤1/3)(κ:ε*(2*R+4*R*R)≤Ξ^3) (clean:∀ a∈ L,a.feel τ t X.1)(move:∀ a∈L,Agrees a.broad X.2 X.1)(x':∀ a∈L,a.rev=b)
    (T:Finset (Seat n))(hx:Disjoint T (whereV L)) (C:FC (Single n))(J: Fine (Tset n) (modesIn n T) false C) (Φ Θ: Wave (Single n)) (c:0<Ξ)(d': Ξ ≤1)(h0:0<k)(g':0<R)(W:Sea (spar j M X.2) Φ)(U:Sea (cutM (Tset n)) Θ) :
    Yep Ξ⁻¹ (acts (star (probe L X*C)) Θ) Φ ((Ξ * (2*R+3))^(L.length*k) *‖C‖) :=by
 obtain ⟨x,y,z',s,t⟩:= summerRay h p g u z v k₁ E κ clean move x' T hx C J
 let I':= fir L; have he:I'.length=L.length*k:= by unfold I' fir; rw [List.length_product]; simp
 have hv:I'.Nodup:= (h.nodup h0).attach.product (List.nodup_ofFn_ofInjective injective_id)
 rw [packsProd (fun i=> handy b (Tset n) (x i) (z' i)) X t,←he]; exact forded s (p.projection _ z) W U c d' (by positivity) I' hv
end Cliplet
end YM.CF.Pannier.Chancel
#print axioms YM.CF.Pannier.Chancel.Cliplet.dropping
