import YM.SU5.Relativistic.Outnumber
import YM.SU5.FiniteGaugeData.Pannier.Fragile
/-!
# Joined analytics on one orientation subcompany (disjoint stamps). Adapts TallPea,
 allows per-basis Z from lookahead stencils in *any* footprint. On good chamber
 with local view to arbitrary halo, each remains a φ-approx fill. Then correct by a
 uniform tilt cost. Crucial for many copies and many X sites in each. 
Registers exact *interacting* filled subwaves on the repaired gauge and
sparse requested points via Tilt, at all Male. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.ScreeV
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Cliplet RG Brace
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {n:Side} {j k d w t:ℕ} {M:Tulip.Male}
variable {μ:ℕ} {ε γ γ' ε' δ τ E' R:ℝ}{L:List (Cliplet n k)}
variable (h:Company j M w d μ t γ γ' τ E' R L)
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
omit h in
private lemma far_caps {S T:Finset (Seat n)}{x:Ket (Single n)}(p:withinM (modesIn n S) x) (d:Disjoint S T): withinM (modesIn n T)ᶜ x:=by
 apply within_more p; intro k h; simp only [modes_at,mem_compl] at *; exact disjoint_left.mp d h
omit h

-- broad-local payment, from Winter on the actual period Torus (Male any)
private lemma concerns {u:ℕ}{δ0:ℝ}{b:Bool}{D:Finset (Seat n)}{A B:Pane n}{x:Ket (Single n)}(p:Sparkle n δ0 M j)(g:Winter j δ n γ u ε)
    (q:0≤δ)(z:Guard A δ0)(e:δ0≤δ)(V:Seat n→ SU.E)(s:withinM (modesIn n D) x)(f: ‖x‖≤ R)
    (af:Agrees (Lattice.halo u D) A B)(hf:Rightful (Lattice.halo u D) (Lattice.gauge V B) 1 γ) (a:‖acts (sp b j M (1:Pane n)) (acts (tradew n V).val x)-acts (tradew n V).val x‖ ≤ E'):
      ‖acts (sp b j M A) x-x‖≤ ε*R+E':=by
 let U:=Lattice.gauge V A; let P:=sp b j M U; let Q:=sp b j M (1:Pane n); let Y:=tradew n V; let y:= acts Y.val x
 have hp:Rightful (Lattice.halo u D) U 1 γ:=by
    apply (riotPort ..).2; intro l hl; refine (show _ ≤ γ from ?_)
    rw [show U l=(Lattice.gauge V B) l by unfold U; unfold Lattice.gauge; rw [af l (mem_filter.mp hl).2.1 (mem_filter.mp hl).2.2]]
    exact (riotPort ..).1 hf l hl
 have hu:‖(P-Q)*Vo D‖ ≤ ε:= hearthB_wind g q ((z.cov V).shrink e) hp
 have ht: acts Y.val (acts (sp b j M A) x)=acts P y:= act_field x (by unfold Y P sp; rw [handAgainst,p.covary _ _ z])
 rw [←act_unit_norm Y (acts (sp b j M A) x-x),map_sub,ht]; change ‖acts P y-y‖≤ _; apply (norm_sub_le_norm_sub_add_norm_sub (acts P y) (acts Q y) y).trans; refine add_le_add ?_ a
 rw [←act_sub,show acts (P-Q) y=acts ((P-Q)*Vo D) y from (by rw [act_mul,show acts (Vo D) y=y from coverSense.mpr s])]; exact (Flare.opy ..).trans (mul_le_mul hu ((act_unit_norm Y x).trans_le f) (norm_nonneg y) ((norm_nonneg _).trans hu))

section abstract
variable {ι:Type*}[LinearOrder ι][Fintype ι][Nonempty ι]
-- warmed tilt: sends to a filled vector with cost without care for number of Vo
lemma remedy (T:UNI ι){P Q:Op ι}(v:IsStarProjection Q)(h:twist T P=Q){x:Ket ι}{S:Finset ι}
    (s:twist T (cutM S)=cutM S)(z:IsUnit (Fock.padded S Q))(r:‖(Fock.padded S Q)⁻¹‖≤R)(p:‖acts P x - x‖≤ ε) : ∃ y:Ket ι,
      acts P y=y ∧ ‖x-y‖ ≤ ε+R*ε ∧ ∀ (i:Ket ι),withinM S i→inner ℂ i y = inner ℂ i x:=by
 let W:= acts T.val x; let G:=cutM S; let Y:=acts Q W; have hp:‖W-Y‖≤ε:=by rw [norm_sub_rev]; unfold Y W; rw [←act_field _ h, ← map_sub, act_unit_norm]; exact p
 let F:=acts G (W-Y); let Z:=warmth Q S F
 let X:= Y+Z; have he:withinM S F:=by unfold withinM; change acts G F= F; unfold F; rw [←act_mul (cutM S) G,show _ * G=G from (cutM_idp _).isIdempotentElem]
 have hx: acts Q Y=Y:= by unfold Y; rw [←act_mul,v.isIdempotentElem.eq]
 have hf:acts G X=acts G W:=by rw [show X=Y+Z from rfl,map_add,show acts G Z=F from warmed z he]; unfold F; rw [map_sub]; abel
 let U:=acts (star T.val) X; have ht: acts T.val U=X:=act_starUnit ..
 refine ⟨U,trim_return h (show trim Q (acts T.val U) from ?_),?_,fun i w=>?_⟩
 · rw [ht]; unfold trim; rw [show X=Y+Z from rfl,map_add,hx,show acts Q Z=Z from server_sh v F]
 · rw [←act_unit_norm T (x-U),map_sub,ht]; apply (norm_sub_le_norm_sub_add_norm_sub W Y X).trans; apply add_le_add hp; rw [show Y-X= -Z from (by unfold X; abel),norm_neg]; exact (shore_cost v _).trans ((Flare.opy ..).trans (mul_le_mul r ((shore_cost (cutM_idp S) _).trans hp) (norm_nonneg F) ((norm_nonneg _).trans r)))
 rw [←act_unit_inner T i U, ←act_unit_inner T i x, ht]; let i':=acts T.val i; change inner ℂ i' X=inner ℂ i' W
 have hh (x:Ket ι): inner ℂ i' x= inner ℂ i' (acts G x):=by rw [←act_inner]; congr 1; rw [(show star G=G from (cutM_idp _).isSelfAdjoint)]; exact (trim_field s w).symm
 rw [hh X,hf,←hh W]
end abstract
open scoped Classical
include h
lemma assemblage {v:Fields n}{b:Bool}{δ0 C E:ℝ}
    (p:Sparkle n δ0 M j)(g:Winter j δ n γ w ε)(q:0≤δ)(z:Guard v.2 δ0)(e:δ0≤δ)
    (p':Winter j δ n γ' μ ε')(u: ∀ S:Finset (Seat n),Sparse d S→ HearthB C (sp b j M (1:Pane n)) S)(s:ε*C≤1/3)
    (e': (ε'*R+E')+(2*C)*(ε'*R+E') ≤ E) (Q:∀ a∈L,a.rev=b ∧ a.feel τ t v.1 ∧ Agrees (hot a μ) v.2 v.1) (T:Finset (Seat n))(t':Disjoint T (whereV L)):
    ∃ x y y': (berries L× Ring5)→ Ket (Single n),
        (∀ i,trim (hand (!b) (cutM (Tset n))) (x i)) ∧ (∀ i,‖x i‖ ≤ 1) ∧
        (∀ i,trim (sp b j M v.2) (y i)) ∧ (∀ i,‖y i‖ ≤ R+E) ∧
        (∀ i,withinM (modesIn n T)ᶜ (y' i)) ∧ (∀ i,‖y' i - y i‖ ≤ E) ∧
        (∀ i l, inner ℂ (x i) (y l) = if i=l then 1 else 0) ∧ (∀ i l, inner ℂ (x i) (y' l) = if i=l then 1 else 0) ∧
        (∀ i,‖y' i‖≤ R) ∧
        (∀ a:Actor L,a.val.frame v=xpert (fun j=>prime (fun c=>handy b (Tset n) (x ((a,j),c)) (y' ((a,j),c))))) := by
 classical
 choose V X Z ri fi ca tr qr wt qt un ra using (fun a:Actor L=> (h.granted a.val a.property).peak v)
 have Q'(a:Actor L):a.val.rev=b:= (Q _ a.property).1
 simp_rw [Q'] at fi tr ra
 let J:= (Cliplet.berries L)×Ring5; let x(i:J):=X i.1.1 i.1.2 i.2; let y(i:J):=Z i.1.1 i.1.2 i.2
 have hV(i:Actor L): Rightful i.val.broad (Lattice.gauge (V i) v.1) 1 γ∧ Rightful (hot i.val μ) (Lattice.gauge (V i) v.1) 1 γ':= ri i (Q _ i.property).2.1
 obtain ⟨G,H⟩:= garment h V
 let A:=Lattice.gauge G v.2; let P:Op (Single n):=sp b j M A; let P':Op (Single n):=sp b j M v.2; let S:=Stripes L; let B:=tradew n G; let S':=modesIn n S
 have hg: Rightful (Lattice.halo w S) A 1 γ:= mustInterpret h (fun i b y z=> (Q _ i.property).2.2 b (halo_subset _ _ y) (halo_subset _ _ z)) H (fun i=> (hV i).1)
 have ht: HearthB (2*C) P S := hearthB_stands (u S h.sparse) (hearthB_wind g q ((z.cov G).shrink e) hg) s
 have hx: twist B P'=P:= by unfold P P' sp B; rw [handAgainst,p.covary _ _ z]
 choose Y U YU atY using (fun i:J=> remedy B (P:=P') (Q:=P) (raft b (p.projection _ (z.cov G))) hx (gauge_frost S G) ht.1 ht.2 (concerns p p' q z e (V i.1.1) (wt i.1.1 i.1.2 i.2) (qt ..) (Q _ i.1.1.property).2.2 (hV i.1.1).2 (ra ..)))
 have hr(i:J): withinM (modesIn n i.1.1.val.s) (x i):= Cliplet.cargo_le i.1.1.val (ca ..)
 have hY(i j:J): inner ℂ (x i) (y j)= if i=j then 1 else 0:=by
    obtain ⟨⟨a,i⟩,k⟩:=i; obtain ⟨⟨l,j⟩,c⟩:=j; unfold x y; dsimp only
    by_cases e:a=l
    · subst l; rw [un]; split_ifs with g f t
      · rfl
      · obtain ⟨rfl,rfl⟩:=g; exact (f rfl).elim
      · exact (g ⟨(congrArg (fun x:J=>x.1.2) t),(congrArg Prod.snd t)⟩).elim
      rfl
    rw [if_neg (show ¬ ((a,i),k) = ((l,j),c) from fun H=>e (Prod.mk.injEq a i l j |>.mp ((Prod.mk.inj H).1) |>.1))] -- tune
    let s':=a.val.broad; let W:=cutM (modesIn n s'); let x':= X a i k; let z':= Z l j c
    have hp:acts W x'=x':= within_more (show withinM (modesIn n a.val.s) x' from hr ((a,i),k)) (modes_monotone (h.granted _ a.property).enter)
    have he: acts W z'=0:= within_compl.mp (far_caps (wt l j c) (h.distinct l.property a.property (fun Y=> e (Subtype.ext Y.symm)))) -- missing h?
    change inner ℂ x' z'=0; rw [←hp,← show star W=W from (cutM_idp _).isSelfAdjoint,act_inner,he,inner_zero_right]
 refine ⟨x,Y,y,fun i=> tr ..,fun i=> qr ..,U,?_,fun i=> far_caps (within_more (wt ..) (modes_monotone (where_ge L i.1.1.property))) t'.symm,fun i=> (YU i).trans e',fun i l=> (atY l _ (within_more (hr i) (modes_monotone (stripes_ge L i.1.1.property)))).trans (hY i l),hY,fun i=> qt ..,fi⟩
 intro i; apply (norm_le_norm_sub_add (Y i) (y i)).trans; rw [norm_sub_rev,add_comm R]; exact add_le_add ((YU i).trans e') (qt ..)
end YM.CF.Pannier.Chancel.ScreeV
#print axioms YM.CF.Pannier.Chancel.ScreeV.assemblage
