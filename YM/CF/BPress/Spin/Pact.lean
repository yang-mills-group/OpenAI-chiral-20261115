import YM.CF.BPress.Spin.Clan
import YM.CF.BPress.Pf.Anchor
/-! pre-pivot cards, all powers constant. `Worthy` schedule fixes thresholds supporting nonlinear Fock bound on all fields. `Voucher` purchases compression bands after (in particular can use any chosen gap width). In applying with these hypotheses, rho* ∈ [0,1) can include uniform strict slack for radC of actual matrix paths]. `Front` supplies `Issued`, proof on the *angular* field when ready.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Spin
open Function Filter NormedSpace Finset Fock Lattice SU Lat Cube Tenant Branch Tulip Scroll Dial Paint Hole Eye Thera Nacre Laic Stride Quad Blank Cellar Cellar.Pass Pf
open scoped Hole Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra

variable {N:Side}{A B W:Pledge}{c d σ ρ q:ℝ}

/-- Speed qH bought independently of D, Pearl and d. Allow using any r>0 prior (in particular (1-r*)/100) for wash error; choose later r ≤ target paid C‖ in compression purchase. N large threshold also independent. -/
structure Worthy (A B W:Pledge) (j:ℕ)(e q r:ℝ)(w:ℕ):Prop where
 above : 1 ≤ j
 q_pos: 0<q
 r_pos:0<r
 speed (N:Side){d:ℝ} :0<d→d ≤ e→w≤ N.val→Shelf N d j A ∧ ∀x:OpenW N d,∀M:Jill.Male,∀ R:Aim N, R.toll B.rate W.rate B.price W.price→ let Y:= spar j M x.val; let T:=Ts R Y x.val
   ‖T‖≤1∧ ∀ U:Paint (More N), MatPlan U→ Bend U x.val q→∀t:ℝ, ‖t‖≤1→ ‖wash (tilt Y T t) (coupling U)‖≤r
lemma purchase_heat (B W:Pledge)(j:ℕ)(h:1≤j)(r:ℝ)(p:0<r): ∃ A e q w,0<e∧ Worthy A B W j e q r w := by
 obtain ⟨d,t,v,A,x,s,T⟩:= purchase_speed j h B W p (k:=1) zero_lt_one; exact ⟨A,d,t,v,x,h,s,p,fun N {d} u l k=> T N k d u l⟩
variable {j w:ℕ}{e r α ε δ:ℝ} {width:Side}
structure Voucher (U:Worthy A B W j e q r w) (width:Side)(ρ σ r':ℝ) (R v:ℕ)(ε δ:ℝ):Prop where
 self (N:Side) (d:ℝ) (x:OpenW N d){G:BandWidth}{X:Bands (More N) G}: G.D=width.val→v≤N.val→0<d→d≤ e→∀P:Support N, Dark X P→∀ L:Aim N, L.toll B.rate W.rate B.price W.price→∀ M:Jill.Male, Uprice R δ P x.val → Meets ε P (shadow j M L x.val)
   ∧ ∀ H:Paint (More N),MatPlan H → Bend H x.val q → ∀ t:ℝ,‖t‖≤1→ (Secret P H σ δ R∨(t=0∧Census P H σ ρ R))→ Pf.Bore (smoothP (Hole.pos P) (Hole.neg P) (loose P) (shadow j M L x.val) t) (coupling H) r'
 ok:w≤ v
 grant:r' <1
 supportK:r ≤ r'
 alive :0<ε
 small:ε≤1
 ball:0<δ
namespace Voucher
variable (U:Worthy A B W j e q r w)
lemma cost {k:ℕ}(t:c≤d)(X:Support N)(g:Bkg (More N))(H:Uprice k c X g) : Uprice k d X g:= fun i x y=>(H i x y).trans t -- tune k
lemma up {a b:ℕ}(ha:a≤b)(X:Support N)(g:Bkg (More N))(h:Uprice b c X g): Uprice a c X g:=by -- tune hypothesis
 apply chord.Close.smaller _ _ _ h; exact Lattice.Corona.halo_mono ha le_rfl
lemma buy (f:r≤ρ)(h: ρ <1)(t:1≤σ)(width: Side):∃ r' R v δ ε,Voucher U width ρ σ r' R v ε δ:=by
 obtain ⟨g,x,y,c,s,hc,H⟩:= holes A B W j U.above width; let ε:=min c 1; have he:0<ε:=lt_min hc one_pos; have hx:ε≤1:= min_le_right ..; have hp:0 <ρ:=U.r_pos.trans_le f; obtain ⟨P,T⟩:=shadow_budget A B W; obtain ⟨r',δ,R,v,h',v',u',k⟩:=clan_control P he hx σ ρ hp.le h; let a:= min g δ; let b:=x+R; refine ⟨r',b,w+y+v,a,ε,⟨?_ ,by omega,v', f.trans h'.le,he,hx,lt_min s u'⟩⟩; intro N d Y G X z hN hd e C u Q H' M J
 have l: 0< a:= lt_min s u'; have ht:=U.speed N hd e (by omega); have hv:= ht.1; let D(S:OpenW N d) := shadow j M Q S.val; have TX(u0:OpenW N d)(t: Uprice b a C u0.val): Meets ε C (D u0):= wage hc he.le (min_le_left ..) (H (by omega) hd.le hv z C u u0 (up (b:=b) (by unfold b; omega) _ _ (cost (min_le_left g δ) C _ t)) M Q H'); -- shadow H'
 let y0:=TX Y J; refine ⟨y0,fun S L V m t0 h0=>?_⟩; let Q':Painted D ε σ:=⟨(Y,C,S), y0, fun x=>(MatPlan.one L x).trans t⟩
 have hA:= shadow_live hv M Q; let n:= shadow_zero hv hd.le M Q; let Z:OpenW N d:=⟨1,guard0 hd.le⟩
 have heY := k d D (by omega) hA (T hv M Q H') Q' (((ht.2 Y M Q H').2 S L V 1 (by simp)).trans f) Z rfl (show Boots (D Z) from ?_) (TX Z (fun i x y=> by change chord (1:E) 1≤ a; rw [chord.refl]; exact l.le)) (up (b:=b) (by unfold b; omega) _ _ (cost (min_le_right g δ) C _ J)) m t0 ?_
 refine ⟨(passed (hA _) he hx y0).stamped m t0,Paint.unit S L,Paint.skew S L,heY,v'⟩
 · intro i P; change shadow j M Q 1 *_= _*cc (shadow j M Q 1); rw [n]; exact free_anti j U.above M i
 rcases h0 with ⟨i,g,Q⟩ | ⟨g,h⟩; refine Duty.upfront ⟨i,g,?_⟩; intro i p; apply (Q _ (Lattice.Corona.halo_mono (show R≤ b by unfold b; omega) le_rfl p)).trans (min_le_right ..); refine Duty.ended g (fun l i=>?_ ); obtain ⟨j,M,t⟩:= h l i; exact ⟨j,M,fun x e v'=> t x e (by unfold b; omega)⟩
end Voucher
end YM.CF.BPress.Spin
