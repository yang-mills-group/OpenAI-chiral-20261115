import YM.SU5.Selected.Attic.Rusk
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
open Chancel.Attic Dais.Parity
namespace Alternative
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

def limitO (t:ℝ)(z:ℕ)(J:ℝ) := t⁻¹^z*J
lemma limitP (h:1≤J){v:ℝ} (t:0<v)(g:v≤1)(d:ℕ): 1≤limitO v d J:=one_le_mul_of_one_le_of_one_le (one_le_pow₀ ((one_le_inv₀ t).mpr g)) h
-- cost α^G * M'^D length, G active D inactive. α bound paid in lump by geometry. avoids exp v^-d requiring h taller. J fixed. Cdirty bound from Hunger. logarithm free, pay linear J'×dust. y= exponent/t power large. need log penalty? d huge a priori; pressure comparison absorbs any κ ⇒ OK.
private lemma arch (L G D Y:ℕ) (K T H:ℝ) (e:L=G+D) (p:L ≤ 2*G+Y) (h:1≤K)(f:0<H)(v: H ≤ K⁻¹^2 * Real.exp (-(2*T))) (t:0≤T): H^G*K^D ≤ Real.exp (-T*(L:ℝ) + (T+K)*(Y:ℝ)):=by
 let b:=Real.log K; have hb:0≤b:= Real.log_nonneg h; have hk: K=Real.exp b:= (Real.exp_log (zero_lt_one.trans_le h)).symm
 have he : K⁻¹^2 * Real.exp (-(2*T))=Real.exp (-(2*(T+b))):=by nth_rw 1 [hk]; rw [←Real.exp_neg,←Real.exp_nat_mul,←Real.exp_add]; push_cast; ring_nf
 apply (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ f.le (v.trans_eq he) G) (pow_nonneg (zero_le_one.trans h) _)).trans
 have hT: K^D=Real.exp b^D:=congrArg (·^D) hk; rw [hT,←Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_add]; push_cast; apply Real.exp_le_exp_of_le; have h₁:(L:ℝ)≤ 2*(G:ℝ)+Y:=by exact_mod_cast p
 have h₂:D≤ L:=by omega
 have h₃:b≤K:= (Real.add_one_le_exp b).trans' (le_add_of_nonneg_right (by norm_num)) |>.trans_eq hk.symm; nlinarith only [mul_le_mul_of_nonneg_left h₁ (show 0 ≤ T+b by positivity), mul_le_mul_of_nonneg_left (Nat.cast_le.mpr h₂) hb,mul_le_mul_of_nonneg_right h₃ (Nat.cast_nonneg (α:=ℝ) Y)] -- generic D≤L. |>. syntax
-- At one sign itinerary. specialize k=1.
variable {y:ℕ}{A0: Orbit n→ Pane n}
open Damask
noncomputable def capDebt(y:ℕ)(t:ℝ)(J T:ℝ)(r:ℕ):ℝ:= (T+limitO t y J)*(4*(r+r+1)^4:ℕ)
theorem poolTilt
    (u:ℝ)(l:ℕ) (g:Service M j w t τ η ξ J R δ q 1 L) (H:Huts y L)(q':Winter j δ n γ w ε)
    (roof: Roof n u δ' l A0)(hq:τ≤u)(ht:l≤t)(hv:δ'≤δ) (r:0<R)(hc:1≤J)
    (e a:ℝ)(c:0<e)(c':e≤1)(tA:0<a)(u':a≤1)(Y1:η+(ξ+ε*R)≤1/3)(Y2:ξ+ε*R+(R*2)*(η+(ξ+ε*R))≤e^3)
    (p':0≤η)(Z:0≤ξ)
    (T:ℝ)(m:0≤T)(f:J*southern e a (2*R) ≤ (limitO a y J)⁻¹^2 * Real.exp (- (2*T)))
    (x:Orbit n)(W Θ:Wave (Single n))(P:IsStarProjection (spar j M (A0 x)))(W':Sea (spar j M (A0 x)) W)(U':Sea (cutM (Tset n)) Θ):
    Yep (e⁻¹*a⁻¹) (acts (star (guest L (x.1,A0 x))) Θ) W (Real.exp (-T * L.length+capDebt y a J T t * flakes τ x.1)* tiltLoan Θ (spar j M (A0 x)) a):=by
 let X:Fields n:=(x.1,A0 x); obtain ⟨D,F,b,l',g',hp,pF,h0,hZ⟩:=orders (by decide) g X; let Y:=guest D; let G:=guest F
 let K:=limitO a y J; have hK:1≤K:= limitP hc tA u' _; let A:=southern e a (2*R); have hA:0<A:=by unfold A southern; positivity
 let V:=Resort F
 have hJ:0<J:= zero_lt_one.trans_le hc; let V':= tiltLoan Θ (spar j M (A0 x)) a; have h':0≤ V':= norm_nonneg _
 have hh:A≤1:=by
    have hk:(K⁻¹)^2≤1:=pow_le_one₀ (inv_pos.mpr (zero_lt_one.trans_le hK)).le (inv_le_one_of_one_le₀ hK); refine (le_mul_of_one_le_left hA.le hc).trans (le_trans f ((mul_le_of_le_one_left (Real.exp_pos _).le hk).trans ?_)); exact Real.exp_le_one_iff.mpr (by nlinarith only [m])
 let HH:=g.less g'; have he:guest L X=Y X * G X:= (Service.prod_perm g pF X (by decide)).trans (by rw [guest_comb]; rfl)
 let HE:= grains (U:=X) (T:=V) (A:=guest F X) (g.less l') q' c c' tA u' hh r Z p' Y1 Y2 ((roof.paid x).shrink hv) P W' U' (fun i h=>(hZ i h).1) (fun i h y₀ e p=>Eq.symm ((show Agrees i.broad X.2 X.1 from fledged roof i.broad x hq (Disjoint.mono_left (Corona.halo_mono ht le_rfl) (show Disjoint (Lattice.halo t i.broad) (flags τ X.1) from (hZ i h).1))) y₀ e p)) (fun i h=>(hZ i h).2) (huts_price (y:=y) (L:=F) (fun i p=>H i (g'.mem p)) X) ((HH.permit (subset_refl V)).allV X) hp
 rw [show guest L (x.1,A0 x)=Y X*G X from he]; refine HE.weigh (mul_le_mul_of_nonneg_right ?_ h') (by positivity)
 rw [mul_assoc, Nat.mul_one]; refine le_trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg (mul_pos hJ hA).le D.length)) (le_trans (arch L.length D.length F.length ((roughness τ x.1).card*(4*(t+t+1)^4)) K T (J*A) (by simpa only [List.length_append] using pF.length_eq) h0 hK (mul_pos hJ hA) f m) ?_)
 · unfold K limitO; rw [mul_pow,pow_mul]; apply mul_le_mul_of_nonneg_left _ (by positivity); simpa only [Nat.mul_one] using HH.guests_v X hJ.le -- tune
 unfold capDebt flakes; apply le_of_eq; push_cast; unfold K; ring
end Alternative
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Alternative
#print axioms poolTilt
#print axioms arch
