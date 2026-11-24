import Lucent.Lease
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.Lucent
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Buffered Buffered.Lifted Skye MeasureTheory NormedSpace
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
open Ballad EmberWind Window Lamour.Bridge Celeste
open WakeInvestment


open Peaks Scree
open Pannier.Chancel Py.Rate.Pannier
open Cube Laic Buffered.Afterglow Journey Dial
open Rous Pressure Worth
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
variable (s i k:ℕ)
set_option quotPrecheck false
local notation "■" => RootBook Y i k s
local notation "ℕ'" => side Y i s
local notation "flatP" => Dial.spar P.K.j (RootBook Y i k s).J.M (1:Pane (side Y i s))
open Buffered.Afterglow
open Window Cliplet

/-- Noble prices at constant color frame. Thus a Nacreous price,
calculated in a *local* gauge frame, has a true gauge-invariant admission. -/
private lemma constant_flat (g:SU.E) :
    let T:= quantU (tradew (side Y i s) (fun _ => g))
    acts T.val (flatSea Y s i k)=(flatSea Y s i k):=by
 intro T
 let p : Seat ℕ'→SU.E:=fun _=> g
 have hv:=Hive.honey_x P.W.pearl P.V.note (P.J.gran.trans ((Y.voyage i).ownership s).size) (nontrivial_spin P) (M:=(RootBook Y i k s).J.M) (guard0 P.dpos.le) p
 have hg:Lattice.gauge p (1:Pane ℕ') = 1 := by funext i; change g * 1 * g⁻¹ = 1; rw [mul_one,mul_inv_cancel] -- tune
 rw [hg] at hv; exact hv.symm

lemma constant_noble (g:SU.E)(F:FC (Single ℕ')) :
    noble Y s i k (twist (quantU (tradew (side Y i s) (fun _ => g))) F)= noble Y s i k F := by
 unfold noble; let V:= fun (_:Seat ℕ')=>g; let T:=quantU (tradew _ V)
 let x:=mateK ℕ'; let y:=flatSea Y s i k; have h:=act_unit_inner T x (acts F y); rw [show acts T.val x=x from Girt.mastC _,Fock.swivel,show acts T.val y=y from constant_flat Y s i k g] at h; exact congrArg (· / inner ℂ x y) h

variable {I:Type} [Fintype I] (W:I→Staff)
abbrev press (L:List (Loop I)):ℂ:=noble Y s i k (spind ℕ' W L)
def plafond (I:Type)[Fintype I](d:ℕ)(M:ℝ):ℝ:=sizeRent (2*d) (Fintype.card I)* flatTicket M^(2*d)
lemma plafond_pos {M v:ℝ}(h:Investment P M v)(d:ℕ):0<plafond I d M:=by unfold plafond sizeRent; have hb:=flatT_pos h; positivity
lemma press_pay {M v:ℝ}(h: Investment P M v)(L:List (Loop I)) : ‖press Y s i k W L‖ ≤ plafond I L.length M:=by
 let F:= WakeInvestment.weighted flatP 0 (flatShear Y s i k); let X:=spind ℕ' W L; let d:=2*L.length; let V:=modesIn _ (rooks W ℕ')
 have hv: Lyrics V d (sizeRent d (Fintype.card I)) X:=by
    refine (spind_cost ..).output.expend le_rfl ?_
    rw [one_mul]; exact size_issue (rooks_card W) d
 exact (noble_bound Y s i k X 0).trans (hv.post F (invest_W Y s i k h _ (by norm_num)) (flatT_pos h))

variable (S:Stencil I)
def icing (x:Tint I→ℝ):ℂ:=S.quote (fun a=>glint x a.flash * press Y s i k W a.loom)
lemma iced (G:I→SU.group.Color) :
 noble Y s i k (dream ℕ' W S G)= icing Y s i k W S (hues G):=by
 let U:= Lamour.alleyR (mateK ℕ') (flatSea Y s i k)
 rw [noble_linear,dream,
    ← Stencil.quote_lift (g:=U) (t:=map_zero U) (p:=map_add U) (u:=map_smul U)]
 unfold icing; apply Stencil.quote_congr; intro j _
 change U (glint _ _ • spind ℕ' W j.loom)= _ * press Y s i k W _; unfold press; rw [map_smul,noble_linear]; rfl

lemma dues_pos :0≤ dues S:=by cases S with|mk L=>induction L with|nil=>exact le_rfl|cons i l h=> exact add_nonneg (norm_nonneg _) h
lemma quote_cost (g:Join I→ℂ)(R:ℝ)(p:∀ b∈S.out,‖g b.toJoin‖≤R): ‖S.quote g‖≤ dues S*R:=by
 cases S with|mk L=>
 induction L with
 | nil=> simp [Stencil.quote, dues]
 | cons q L ih=> rw [Stencil.cons_q,dues_cons,add_mul]; apply (norm_add_le ..).trans; rw [norm_smul]; exact add_le_add (mul_le_mul_of_nonneg_left (p _ List.mem_cons_self) (norm_nonneg _)) (ih fun v k=>p v (List.mem_cons_of_mem _ k))
lemma quote_sub (g f:Join I→ℂ) : S.quote g-S.quote f=S.quote (fun i=>g i-f i):=by
 cases S with|mk L=>induction L with
 | nil=> exact sub_self 0
 | cons i L ih=> rw [Stencil.cons_q,Stencil.cons_q,Stencil.cons_q, smul_sub,←ih]; abel
variable {x y: Tint I→ℝ}
lemma iced_cont: ContDiff ℝ 1 (icing Y s i k W S):=by
 cases S with|mk L=>induction L with
 | nil=> exact contDiff_const
 | cons j l h=>
    rw [show icing Y s i k W {out:=j::l}=(fun x=>j.k • (glint x j.flash * press Y s i k W j.loom)+icing Y s i k W {out:=l} x) from rfl]
    exact ((show ContDiff ℝ (1) (fun _:Tint I→ℝ=>j.k) from contDiff_const).smul ((glint_c j.flash).mul contDiff_const)).add h

def candied (S:Stencil I)(M:ℝ)(m d:ℕ):ℝ:= dues S * (1+m)*plafond I d M

variable {M v B:ℝ} {m d:ℕ}
lemma candied_pos (h: Investment P M v) : 0 ≤ candied S M m d := by unfold candied; have hv:=plafond_pos (I:=I) h d; have hd:=dues_pos S; positivity
lemma iced_cost (h:Investment P M v)(q:S.degree m d) (u:0 ≤ B)(x:Tint I→ℝ)(l:Covers x B): ‖icing Y s i k W S x‖ ≤ candied S M m d * B^m := by
 unfold icing; have hd:0≤dues S:=dues_pos S
 rw [show candied S M m d * B^m = dues S * ((1+m)*(B^m * plafond I d M)) from by unfold candied;ring]
 apply quote_cost; intro j p; rw [norm_mul]
 have ht:=mul_le_mul (glint_le _ u _ l j.flash) (press_pay Y s i k W h j.loom) (norm_nonneg _) (pow_nonneg u _)
 rw [(q j p).1,(q j p).2] at ht
 exact ht.trans (le_mul_of_one_le_left (mul_nonneg (pow_nonneg u _) (plafond_pos h _).le) (le_add_of_nonneg_right (Nat.cast_nonneg _)))

lemma iced_sub (h:Investment P M v)(q:S.degree m d){Z:ℝ} (u:1 ≤ B)(g:Covers x B)(l:Covers y B)(r:Adjoins x y Z)(t:0≤Z): ‖icing Y s i k W S x-icing Y s i k W S y‖ ≤ candied S M m d * B^m *Z := by
 have hb:=zero_le_one.trans u
 unfold icing; rw [quote_sub,show candied S M m d * B^m *Z= dues S * (((1+m)*B^m *Z) * plafond I d M) from by unfold candied;ring]
 apply quote_cost; intro j p; rw [←sub_mul,norm_mul]
 have ht:= glint_sub g u l r t j.flash
 have hv:= press_pay Y s i k W h j.loom
 rw [(q j p).1] at ht; rw [(q j p).2] at hv
 have he: (m:ℝ)≤1+(m:ℝ) := by linarith only
 apply mul_le_mul _ hv (norm_nonneg _) (by positivity)
 exact ht.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he (pow_nonneg hb _)) t)
lemma dressed (h:Investment P M v)(q:S.degree m d){C:ℝ}(r:candied S M m d ≤ C): Regis.Wake.Paint (icing Y s i k W S) m C:= by
 have hx(g: ℝ)(x:Tint I→ℝ)(p:‖x‖≤g): Covers x g:=fun i=> (norm_le_pi_norm x i).trans p

 constructor
 · exact iced_cont ..
 · intro B p x l; exact (iced_cost Y s i k W S h q (zero_le_one.trans p) x (hx _ _ l)).trans (mul_le_mul_of_nonneg_right r (by positivity))
 intro B p x y a b
 exact (iced_sub Y s i k W S h q p (hx _ _ a) (hx _ _ b) (hx _ (x-y) le_rfl) (norm_nonneg _)).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right r (by positivity)) (norm_nonneg _))
