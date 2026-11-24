import YM.SU5.Selected.Lantern.Festival
import YM.SU5.FiniteGaugeData.Pannier.Sheds
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
local notation "I"=>Complex.I
-- adapt Pannier Sheds cost
open Brace
open Py.Rate (sites)
open Py.Rate.Pannier
variable {k j w t:ℕ}{τ J ξ R η δ δ' γ ε:ℝ}{n:Side}
 {M:Tulip.Male}{L:List (Cab n)}{q:Type}[Fintype q][DecidableEq q]
namespace Service
private lemma twoWay {α:Type*} (L:List α)(f:α→Bool)(u:α→Bool): ∃ b:Bool, (L.filter f).length ≤ 2 * (L.filter fun x=> f x && u x==b).length:=by
 let X:=L.filter f; let Y:= X.filter u; let F:= X.filter fun x=> !u x
 have he: (Y++F).Perm X:= List.filter_append_perm u X
 have hp: Y = L.filter (fun x=> f x && u x == true):=by unfold Y X; rw [List.filter_filter]; congr 1; funext x; simp [and_comm,Bool.and_comm] -- tune
 have hf: F= L.filter (fun x=> f x && u x == false):=by unfold F X; rw [List.filter_filter]; congr 1; funext x; cases u x <;> simp
 have hh:Y.length+F.length=X.length:=by simpa only [List.length_append] using he.length_eq
 rcases le_total Y.length F.length with g|g; exact ⟨false,by rw [←hf,show (L.filter f).length=X.length from rfl]; omega⟩
 exact ⟨true,by rw [←hp,show (L.filter f).length=X.length from rfl]; omega⟩
private lemma margin {D F:List (Cab n)}(h:Service M j w t τ η ξ J R δ q k L)(d:D.Sublist L)(f:F.Sublist L)(u:∀ i∈D,i∉ F): Disjoint (Resort D) (Resort F):=by
 apply disjoint_left.mpr; intro x hx hy; obtain ⟨A,g,v⟩:=(resident ..).1 hx; obtain ⟨B,w,hx⟩:=(resident ..).1 hy; exact disjoint_left.mp (h.apart (d.mem g) (f.mem w) (by rintro e; exact u A g (e.symm ▸ w))) v hx
lemma prod_perm {D:List (Cab n)} (h:Service M j w t τ η ξ J R δ q k L)(p:L.Perm D)(x:Fields n)(u:0<k) : guest L x=guest D x:=by
 rw [visits_C,visits_C]; apply (p.map (fun A=> A.frame x)).prod_eq'; rw [List.pairwise_map]; have he(A)(v:A∈ L):Fine (Tset n) univ false (A.frame x):= Window.fine_enlarge (subset_univ _) ((h.guests A v).env.allV x); exact (h.nodup).pairwise_of_forall_ne (fun i hi j hj _=> fineWise (he i hi) (he j hj))
private lemma isDirt {t:ℕ}{u:Finset (Seat n)}{A:(Cab n)}(h:¬ Disjoint (Lattice.halo t A.broad) u) :
    ∃ i∈ A.broad,i∈ Lattice.halo t u:=by obtain ⟨i,h,t'⟩:= Finset.not_disjoint_iff.mp h; obtain ⟨v,q,l⟩:= halo_spec.mp h; exact ⟨v,q,halo_spec.mpr ⟨i,t',(separation_comm ..).trans_le l⟩⟩
private lemma seekNumber {Z:Finset (Seat n)} (d' : 0<k)(h:Service M j w t τ η ξ J R δ q k L)(p:∀ a∈L, ∃ i∈ a.broad,i∈ Z) : L.length≤ Z.card:=by
 induction L generalizing Z with
 | nil=> simp
 | cons a L ih=>
    obtain ⟨x,q,g⟩:= p _ List.mem_cons_self
    have ht:L.length≤ (Z.erase x).card:=by
      apply ih (h.less (by simp)); intro i u; obtain ⟨y,t,v⟩:= p i (List.mem_cons_of_mem _ u); refine ⟨_,t,mem_erase.mpr ⟨fun k=> ?_,v⟩⟩; exact disjoint_left.mp ((List.pairwise_cons.mp h.border).1 i u) q (k ▸ t) -- nested eq
    rw [Finset.card_erase_of_mem g] at ht; rw [List.length_cons]; have ho:= Finset.card_pos.mpr (show Z.Nonempty from ⟨x,g⟩); omega
private lemma orders (d':0<k)(h:Service M j w t τ η ξ J R δ q k L) (V:Fields n) :
    ∃ (W D:List (Cab n))(u:Bool), W.Sublist L ∧ D.Sublist L ∧ Disjoint (Resort W) (Resort D) ∧ L.Perm (W++D) ∧
    L.length ≤ 2*W.length+ (roughness τ V.1).card * (4*(t+t+1)^4) ∧ ∀ a∈W,a.feels V t τ ∧ a.rev=u:=by
 classical
 let f(a:Cab n):= decide (a.feels V t τ); let F:=L.filter f; let K:= L.filter (fun a=> !f a); have p : (F++K).Perm L:= List.filter_append_perm f L; obtain ⟨u,w⟩:=twoWay L f Cab.rev; let g(a:Cab n):= f a && a.rev==u
 let W:=L.filter g; let B:= L.filter fun z=> !g z; have hf:W.Sublist L:=List.filter_sublist; have hg:B.Sublist L:=List.filter_sublist
 have ht: K.length≤ (roughness τ V.1).card * (4*(t+t+1)^4):=by
    apply (seekNumber (Z:=Lattice.halo t (flags τ V.1)) d' (h.less (show K.Sublist L from List.filter_sublist)) (fun i v=> isDirt ?_)).trans ((Corona.halo_size ..).trans ?_)
    -- goal order
    all_goals first
    | exact (Nat.mul_le_mul_right _ (flag_coat V.1 τ)).trans_eq (Nat.mul_assoc ..)
    | exact (show ¬ i.feels V t τ from by have hk:= (List.mem_filter.mp v).2; simpa [f] using hk)
 have hx:L.Perm (W++B):= (List.filter_append_perm g L).symm
 refine ⟨W,B,u,hf,hg,margin h hf hg (fun i h t=> (by have hp:= (List.mem_filter.mp h).2; have hg:(!g i)=true:= (List.mem_filter.mp t).2; rw [show g i=true from hp] at hg; contradiction)),hx,?_ ,fun i he=>?_⟩
 · calc
   _ = F.length+K.length:= by simpa only [List.length_append] using p.length_eq.symm
   _ ≤ _ := Nat.add_le_add w ht
 have t: g i=true:= (List.mem_filter.mp he).2; simpa [g,f] using t

private lemma scruple (x U Y :ℕ) (Z:ℝ) (h:(x:ℝ)≤ 2*(U:ℝ)+Y) (w:0<R) (v: Y≥0)(e:0≤Z)(k:ℕ) (t:τ ≤ Real.exp (-2*(Z+R)))(hp:0<τ):
    (τ)^(U*k)*(1+R)^(x*k) ≤ Real.exp (-(Z*(x*k:ℕ))+(Z+R)*(Y*k:ℕ)):=by  -- casts last expression coerces?
 have hg:1+R≤Real.exp R:=by linarith [Real.add_one_le_exp R]
 have ht:= pow_le_pow_left₀ (show 0 ≤ τ by positivity) t (U*k)
 apply (mul_le_mul ht (pow_le_pow_left₀ (show 0 ≤ 1+R by positivity) hg (x*k)) (by positivity) (by positivity)).trans
 rw [←Real.exp_nat_mul,←Real.exp_nat_mul,← Real.exp_add]; apply Real.exp_le_exp_of_le; push_cast; have he:0≤Z+R:=by linarith
 have hx:= mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg (α:=ℝ) k)) he; nlinarith only [hx]
open Damask
variable {A0 : Orbit n→ Pane n}
theorem poolPrice
    (u:ℝ)(l:ℕ) (g:Service M j w t τ η ξ J R δ q k L) (q':Winter j δ n γ w ε)
    (roof: Roof n u δ' l A0)(hq:τ≤u)(ht:l≤t)(hv:δ'≤δ) (r:0<R)(hc:1≤J)
    (e:ℝ)(c:0<e)(c':e≤1)(Y1:η+(ξ+ε*R)≤1/3)(Y2:ξ+ε*R+(R*2)*(η+(ξ+ε*R))≤e^3)
    (p':0≤η)(Z:0≤ξ)
    (a A θ:ℝ)(k0:0<k)(m:0≤a)(f:J*(e*(2*R+3)) ≤ Real.exp (-2*(a+J)))(z:a*θ≥A)(v:(L.length*k:ℕ)≥θ*sites n)
    (x:Orbit n)(W Θ:Wave (Single n))(P:IsStarProjection (spar j M (A0 x)))(W':Sea (spar j M (A0 x)) W)(U':Sea (cutM (Tset n)) Θ):
    Yep e⁻¹ (acts (star (guest L (x.1,A0 x))) Θ) W (Real.exp (-(A*sites n)+((a+J)*(4*(t+t+1)^4*k:ℕ))*flakes τ x.1)):=by
 let X:Fields n:=(x.1,A0 x); obtain ⟨D,F,b,l',g',hp,pF,h0,hZ⟩:=orders k0 g X
 have HH:=g.less g'; let Y:= guest D; let G:=guest F; have he:guest L X=Y X*G X:= (prod_perm g pF X k0).trans (by rw [guest_comb]; rfl)
 let V:= Resort F; have heJ:0<J:=zero_lt_one.trans_le hc; have hc':e*(2*R+3) ≤1:= (le_mul_of_one_le_left (by positivity: 0≤ e*(2*R+3)) hc).trans (f.trans (Real.exp_le_one_iff.mpr (by linarith))) -- tune
 let HE:=(g.less l').peels (U:=X) q' c c' hc' r Z p' Y1 Y2 ((roof.paid x).shrink hv) P W' U' (fun i h=>(hZ i h).1) (fun i h a₀ e p=>Eq.symm ((show Agrees i.broad X.2 X.1 from fledged roof i.broad x hq (Disjoint.mono_left (Corona.halo_mono ht le_rfl) (show Disjoint (Lattice.halo t i.broad) (flags τ X.1) from (hZ i h).1))) a₀ e p)) (fun i h=>(hZ i h).2) ((HH.permit (subset_refl V)).allV X) hp -- .Agrees.symm?
 rw [show guest L (x.1,A0 x)=Y X*G X from he]; refine HE.weigh (le_trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by positivity) (D.length*k))) ((scruple L.length D.length ((roughness τ x.1).card*(4*(t+t+1)^4)) a (by exact_mod_cast h0) heJ (Nat.zero_le _) m k f (by positivity)).trans (Real.exp_le_exp_of_le ?_))) (by positivity)
 · apply (HH.guests_v X heJ.le).trans; exact (pow_le_pow_right₀ hc (Nat.mul_le_mul_right _ g'.length_le)).trans (pow_le_pow_left₀ heJ.le (by linarith: J≤ 1+J) _)
 unfold flakes; have he:= mul_le_mul_of_nonneg_left v m; push_cast; push_cast at he; nlinarith only [he,mul_le_mul_of_nonneg_right z (show 0≤ sites n by unfold sites; positivity)]
end Service
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern
#print axioms Service.poolPrice
