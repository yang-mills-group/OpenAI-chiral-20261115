import YM.SU5.FiniteGaugeData.Pannier.TallPea
/-!
# Four-volume budget at density. Distinct clean subset chosen before integrating:
Yep is a pointwise bound even with discontinuous good/dirty designation.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.Pannier.Chancel
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Cliplet RG Brace
open Py.Rate (sites)
open Py.Rate.Pannier
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {n:Side}{k:ℕ}
namespace Cliplet
variable {L:List (Cliplet n k)}{U:Pane n}{j w d t:ℕ}{γ τ R ε δ δ':ℝ}{M:Tulip.Male}
private lemma twoWay {α:Type*} (L:List α)(f:α→Bool)(u:α→Bool): ∃ b:Bool, (L.filter f).length ≤ 2 * (L.filter fun x=> f x && u x==b).length:=by
 let X:=L.filter f; let Y:= X.filter u; let F:= X.filter fun x=> !u x
 have he: (Y++F).Perm X:= List.filter_append_perm u X
 have hp: Y = L.filter (fun x=> f x && u x == true):=by unfold Y X; rw [List.filter_filter]; congr 1; funext x; simp [and_comm,Bool.and_comm] -- tune
 have hf: F= L.filter (fun x=> f x && u x == false):=by unfold F X; rw [List.filter_filter]; congr 1; funext x; cases u x <;> simp
 have hh:Y.length+F.length=X.length:=by simpa only [List.length_append] using he.length_eq
 rcases le_total Y.length F.length with g|g; exact ⟨false,by rw [←hf,show (L.filter f).length=X.length from rfl]; omega⟩
 exact ⟨true,by rw [←hp,show (L.filter f).length=X.length from rfl]; omega⟩
private lemma margin {D F:List (Cliplet n k)}(h:Flight j M w d t γ τ L)(d:D.Sublist L)(f:F.Sublist L)(u:∀ i∈D,i∉ F): Disjoint (whereV D) (whereV F):=by
 apply disjoint_left.mpr; intro x hx hy; obtain ⟨A,g,v⟩:=(whereV_at ..).1 hx; obtain ⟨B,w,hx⟩:=(whereV_at ..).1 hy; exact disjoint_left.mp (h.distinct (d.mem g) (f.mem w) (by rintro e; exact u A g (e.symm ▸ w))) v hx
private lemma prod_perm {D:List (Cliplet n k)} (h:Flight j M w d t γ τ L)(p:L.Perm D)(x:Fields n)(u:0<k) : probe L x=probe D x:=by
 rw [probe_at,probe_at]; apply (p.map (fun A=> A.frame x)).prod_eq'; rw [List.pairwise_map]; have he(A)(v:A∈ L):Fine (Tset n) univ false (A.frame x):= Window.fine_enlarge (subset_univ _) ((h.granted A v).atCost.allV x); exact (h.nodup u).pairwise_of_forall_ne (fun i hi j hj _=> fineWise (he i hi) (he j hj))
private lemma isDirt {t:ℕ}{u:Finset (Seat n)}{A:(Cliplet n k)}(h:¬ Disjoint (Lattice.halo t A.broad) u) :
    ∃ i∈ A.broad,i∈ Lattice.halo t u:=by obtain ⟨i,h,t'⟩:= Finset.not_disjoint_iff.mp h; obtain ⟨v,q,l⟩:= halo_spec.mp h; exact ⟨v,q,halo_spec.mpr ⟨i,t',(separation_comm ..).trans_le l⟩⟩
private lemma seekNumber {Z:Finset (Seat n)} (d' : 0<k)(h:Flight j M w d t γ τ L)(p:∀ a∈L, ∃ i∈ a.broad,i∈ Z) : L.length≤ Z.card:=by
 induction L generalizing Z with
 | nil=> simp
 | cons a L ih=>
    obtain ⟨x,q,g⟩:= p _ List.mem_cons_self
    have ht:L.length≤ (Z.erase x).card:=by
      apply ih (h.shorter (by simp)); intro i u; obtain ⟨y,t,v⟩:= p i (List.mem_cons_of_mem _ u); refine ⟨_,t,mem_erase.mpr ⟨fun k=> ?_,v⟩⟩; exact disjoint_left.mp ((List.pairwise_cons.mp h.lock).1 i u) q (k ▸ t) -- nested eq
    rw [Finset.card_erase_of_mem g] at ht; rw [List.length_cons]; have ho:= Finset.card_pos.mpr (show Z.Nonempty from ⟨x,g⟩); omega
private lemma orders (d':0<k)(h:Flight j M w d t γ τ L) (V:Pane n) :
    ∃ (W D:List (Cliplet n k))(u:Bool), W.Sublist L ∧ D.Sublist L ∧ Disjoint (whereV W) (whereV D) ∧ L.Perm (W++D) ∧
    L.length ≤ 2*W.length+ (roughness τ V).card * (4*(t+t+1)^4) ∧ ∀ a∈W,a.feel τ t V ∧ a.rev=u:=by
 classical
 let f(a:Cliplet n k):= decide (a.feel τ t V); let F:=L.filter f; let K:= L.filter (fun a=> !f a); have p : (F++K).Perm L:= List.filter_append_perm f L; obtain ⟨u,w⟩:=twoWay L f Cliplet.rev; let g(a:Cliplet n k):= f a && a.rev==u
 let W:=L.filter g; let B:= L.filter fun z=> !g z; have hf:W.Sublist L:=List.filter_sublist; have hg:B.Sublist L:=List.filter_sublist
 have ht: K.length≤ (roughness τ V).card * (4*(t+t+1)^4):=by
    apply (seekNumber (Z:=Lattice.halo t (flags τ V)) d' (h.shorter (show K.Sublist L from List.filter_sublist)) (fun i v=> isDirt ?_)).trans ((Corona.halo_size ..).trans ?_)
    -- goal order
    all_goals first
    | exact (Nat.mul_le_mul_right _ (flag_coat V τ)).trans_eq (Nat.mul_assoc ..)
    | exact (show ¬ i.feel τ t V from by have hk:= (List.mem_filter.mp v).2; simpa [f] using hk)
 have hx:L.Perm (W++B):= (List.filter_append_perm g L).symm
 refine ⟨W,B,u,hf,hg,margin h hf hg (fun i h t=> (by have hp:= (List.mem_filter.mp h).2; have hg:(!g i)=true:= (List.mem_filter.mp t).2; rw [show g i=true from hp] at hg; contradiction)),hx,?_ ,fun i he=>?_⟩
 · calc
   _ = F.length+K.length:= by simpa only [List.length_append] using p.length_eq.symm
   _ ≤ _ := Nat.add_le_add w ht
 have t: g i=true:= (List.mem_filter.mp he).2; simpa [g,f] using t

private lemma scruple (x U Y :ℕ) (Z:ℝ) (h:(x:ℝ)≤ 2*(U:ℝ)+Y) (w:0<R) (v: Y≥0)(e:0≤Z)(k:ℕ) (t:τ*(2*R+3) ≤ Real.exp (-2*(Z+R)))(hp:0<τ):
    (τ*(2*R+3))^(U*k)*(1+R)^(x*k) ≤ Real.exp (-(Z*(x*k:ℕ))+(Z+R)*(Y*k:ℕ)):=by  -- casts last expression coerces?
 have hg:1+R≤Real.exp R:=by linarith [Real.add_one_le_exp R]
 have ht:= pow_le_pow_left₀ (show 0 ≤ τ*(2*R+3) by positivity) t (U*k)
 apply (mul_le_mul ht (pow_le_pow_left₀ (show 0 ≤ 1+R by positivity) hg (x*k)) (by positivity) (by positivity)).trans
 rw [←Real.exp_nat_mul,←Real.exp_nat_mul,← Real.exp_add]; apply Real.exp_le_exp_of_le; push_cast; have he:0≤Z+R:=by linarith
 have hx:= mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg (α:=ℝ) k)) he; nlinarith only [hx]
open Damask
variable {A0 : Orbit n → Pane n}
lemma manyYear (u:ℝ)(l:ℕ)(g:Flight j M w d t γ τ L)(p:Sparkle n δ' M j)(p': 0≤δ')(q:Winter j δ n γ w ε)(roof:Roof n u δ' l A0) (hq:τ≤u) (ht:l≤ t) (hv:δ'≤δ)(k₁:∀ S:Finset (Seat n),Sparse d S →∀ b,HearthB R (sp b j M (1:Pane n)) S)(E : ε*R ≤ 1/3) (r:0<R)
    (e:ℝ)(c:0<e)(c':e≤1)(a A η:ℝ)(he:ε*(2*R+4*R*R) ≤ e^3)(k0:0<k) (m:0≤a)(f:e*(2*R+3)≤Real.exp (-2*(a+R)))(z:a*η≥ A)(v:(L.length*k:ℕ)≥η*sites n)
    (x:Orbit n)(W Θ:Wave (Single n))(W':Sea (spar j M (A0 x)) W)(U':Sea (cutM (Tset n)) Θ) : Yep e⁻¹ (acts (star (probe L (x.1,A0 x))) Θ) W (Real.exp (-(A*sites n) + ((a+R)* (4*(t+t+1)^4*k:ℕ))*flakes τ x.1)):=by
 let X:Fields n:=(x.1,A0 x); obtain ⟨D,F,b,l',g',hp₁,pf,hh,hZ⟩:=orders k0 g x.1
 let Y:= probe D X; let G:=probe F X; have Hp:Flight _ _ _ _ _ _ _ D:= g.shorter l'; let H:=g.shorter g'; have he₁:probe L X= Y*G:= (prod_perm g pf X k0).trans (by rw [probe_combine]; rfl)
 have HE:=dropping (X:=X) Hp p q hv (roof.paid x) (p'.trans hv) (fun i u=>k₁ i u b) E he (fun i h=> (hZ i h).1) (fun i h=> Py.Rate.Pannier.fledged roof i.broad x hq ((hZ i h).1.mono_left (Corona.halo_mono ht le_rfl))) (fun i hi=> (hZ i hi).2) _ hp₁.symm G (H.corsage.allV X) _ _ c c' k0 r W' U' -- tune .feel.mono_left
 rw [show (probe L (x.1,A0 x))=Y*G from he₁]; refine HE.weigh (le_trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by positivity) (D.length*k))) ((scruple L.length D.length ((roughness τ x.1).card*(4*(t+t+1)^4)) a (by exact_mod_cast hh) r (Nat.zero_le _) m k f c).trans (Real.exp_le_exp_of_le ?_))) (by positivity)
 · apply (H.capPrice (fun i p=>k₁ i.s (H.granted _ p).far i.rev) (fun b=>raft b (p.projection _ (guard0 p'))) X r.le).trans -- p shadow
   exact pow_le_pow_right₀ (by linarith) (Nat.mul_le_mul_right _ g'.length_le)
 unfold flakes; have he:= mul_le_mul_of_nonneg_left v m;
 push_cast; push_cast at he; nlinarith only [he,mul_le_mul_of_nonneg_right z (show 0≤ sites n by unfold sites; positivity)]
end Cliplet
end YM.CF.Pannier.Chancel
#print axioms YM.CF.Pannier.Chancel.Cliplet.manyYear
