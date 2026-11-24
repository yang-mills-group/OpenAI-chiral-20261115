import YM.SU5.LitCurrent.Initial
import YM.CF.Sour.Stip
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.LitCurrent
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v:ℝ}{r:ℕ}
local notation "I" => Single N
open Salt
abbrev StageTree (N:Side)(d a v:ℝ):=Sour.Elm N Unit d a v
abbrev sky (E: StageTree N d a v) (x:Openc (More N) d) :=∑ F:Sa N,E.F F () x
abbrev moored (o:Seat N)(E:StageTree N d a v):Prop:=∀ S, o∉ S→E.W S=0
lemma issue (p:Soak o X a v d): ∃ E:StageTree N d a v, moored o E∧ ∀ x:Openc (More N) d,X x.val=sky E x:=by
 obtain ⟨F,C,t,u,z,g⟩:=p
 exact ⟨⟨fun S _=>F S,C,fun S=> ⟨fun _=> t S,fun _=>continuous_const⟩, tally_F (fun S=>(t S).nonn) z⟩,u,g⟩
namespace StageTree
variable (E:StageTree N d a v)
def adj : StageTree N d a v:=⟨fun S _=>glaze d (E.F S ()), fun i=> Function.swap (E.W i),fun S=> ⟨fun _=>bits _ _ _ _ ((E.coat S).1 ()), fun _=>continuous_const⟩,E.bank.flip⟩
def repair : StageTree N d a v:=by
 let T:= E.plus (adj E); let X(S i x):= (2:ℂ)⁻¹ • (T.F S i x)
 have ht(s):=(T.coat s).1
 let C (S):= fun i j=> ‖(2:ℂ)⁻¹‖*T.W S i j
 refine ⟨X,C, fun S=> ⟨fun i=>(ht S i).accel _,fun X=> (continuous_const (y:=(2:ℂ)⁻¹)).smul ((T.coat S).2 X)⟩ ,?_⟩
 have h:=T.bank.funds (norm_nonneg ((2:ℂ)⁻¹)); apply h.book; norm_num; linarith
lemma mend (V:Pane N)(x:Openc (More N) d)(p:x.val=profile V)(S:Sa N) : (repair E).F S () x=(2:ℂ)⁻¹ • (E.F S () x+star (E.F S () x)) := by
 change (2:ℂ)⁻¹ • (E.F S () x+star (E.F S () (flit d x)))=_
 have ht : flit d x=x := by
   apply Subtype.ext; change Tulip.ice x.val=x.val; rw [p]; exact ice_pr V
 rw [ht]
lemma repair_self (V:Pane N)(x:Openc (More N) d)(p:x.val=profile V)(S:Sa N): IsSelfAdjoint ((repair E).F S () x):= by
 unfold IsSelfAdjoint; rw [mend E V x p]; rw [star_smul,star_add,star_star,add_comm (star _),star_inv₀,star_ofNat]
lemma mendSky (V:Pane N)(x:Openc (More N) d)(u:x.val=profile V)(p:IsSelfAdjoint (sky E x)): sky (repair E) x=sky E x:=by
 unfold sky; simp_rw [mend E V x u,←smul_sum,sum_add_distrib,←star_sum]
 rw [p.star_eq]; rw [←two_smul ℂ,inv_smul_smul₀ (by norm_num:(2:ℂ)≠0)]
lemma mend_moor (p:moored o E): moored o (repair E):=by
 intro S h; funext i j; change ‖(2:ℂ)⁻¹‖*(E.W S i j+ E.W S j i)=0; rw [p S h]; simp

def lose : StageTree N d a v:=⟨fun S _ x=> -E.F S () x,E.W, fun S=>⟨fun _=>by simpa using ((E.coat S).1 ()).accel (-1),fun x=>continuous_const⟩,E.bank⟩

variable {ι:Type*}(L:ι→ StageTree N d a v)(f:Sweep N→ ι→ι)
lemma moor_frame (i:ι)(u:∀ s:Sweep N,moored ((boxA s).symm o) (L (f s i)))(b0:Bool):
    moored o (haloB L f b0 i):=by
 intro S p; have hp(s:Sweep N):testV s b0 (L (f s i)).W S=0:=by
    have h:=u s (actY s S) (by simpa [actY] using p); funext j k; unfold testV; split <;> simp [tagR,h,Function.swap,noteU]
 funext j k; change ‖(Sour.avg N:ℂ)‖*((∑ s:Sweep N,testV s b0 (L (f s i)).W) S j k)=0
 simp only [Finset.sum_apply,hp,Pi.zero_apply,sum_const_zero,mul_zero]
lemma tree_proj (i:ι) (W:Pane N)(x:↥(Openc (More N) d))(h:x.val=Tulip.profile W)(S:Sa N)(b0:Bool):
    (haloB L f b0 i).F S () x = (avg N:ℂ) • (∑ s:Sweep N,
       realR s⁻¹ b0 ((L (f s i)).F (actY s S) () (Sour.fog s d x))):=by
 change _ • (∑ s:Sweep N, (((L (f s i)).Utar s b0).F S () x))=_
 simp_rw [Sour.Elm.wren _ _ _ _ () W _ h] -- check arg order
lemma frame_proj (i:ι)(W:Pane N)(x:↥(Openc (More N) d))(h:x.val=Tulip.profile W)(b0:Bool): sky (haloB L f b0 i) x=
    (avg N:ℂ) • (∑ s:Sweep N, realR s⁻¹ b0 (sky (L (f s i)) (Sour.fog s d x))):=by
 simp_rw [sky,tree_proj _ _ i W x h,←smul_sum,real_f]; rw [sum_comm]; refine congrArg _ (sum_congr rfl fun s _=>?_)
 refine sum_bij (fun i _=>actY s i) (fun i _=>mem_univ _) (fun i _ j _ g=> map_injective _ g) ?_ (fun i _=>rfl)
 intro i _; exact ⟨actY s⁻¹ i,mem_univ _,by ext; simp [actY,sitU]⟩
end StageTree

/- cardinality cut ready for mask. Track full/tail & root locality. -/
abbrev retain (E:StageTree N d a v)(k:ℕ)(x:Openc (More N) d): Op (Single N):=∑ S:Sa N, if S.card<k then E.F S () x else 0
def beforePing (E:StageTree N d a v)(k:ℕ)(x:Chin N): Op (Single N):= if p:x∈Openc (More N) d then retain E k ⟨x,p⟩ else 0
def beyond (E:StageTree N d a v)(k:ℕ)(x:Chin N): Op (Single N):= if p:x∈Openc (More N) d then sky E ⟨x,p⟩-retain E k ⟨x,p⟩ else 0
abbrev expiry (a v:ℝ):ℝ:= (∑' i:ℕ, Real.exp (-a/2*i)*(Tenant.quota*((i:ℝ)+1)^4))*v
lemma saw_line (E:StageTree N d a v)(p:moored o E)(h:0<a):
    tallyC (a/2) E.W ≤ expiry a v:=by
 refine le_trans (a:=tallyC _ _) ?_ (tall (fun S=>(E.coat S|>.1 ()).toTicket) E.bank h (meterQ ..) (le_trans (by norm_num: (0:ℝ)≤16) quota_bound) o)
 refine le_of_eq ?_; symm; apply sum_subset (subset_univ _); intro S t k; have hx:o ∉ S:=fun H=>k (mem_filter.mpr ⟨mem_univ _,H⟩); change _ * ledgerV (E.W S)=0; rw [p S hx]; simp [ledgerV]
lemma totals (E:StageTree N d (4*a) v)(h:0<a)(p:moored o E)(k:ℕ):
    Trunk o (beforePing E k) k a (expiry (4*a) v) d ∧ Soak o (beyond E k) a (Real.exp (-a*k)*expiry (4*a) v) d:=by
 let W:=E.W; let F(S:Sa N):= E.F S (); let X(S):= if S.card<k then F S else (0:Raw (Openc (More N) d) (Single N)); let Y(S):= if S.card<k then 0 else F S
 let Q(S:Sa N):= if S.card<k then W S else 0; let T (S:Sa N):= if S.card<k then 0 else W S
 have hx(S):Suite (badge _) (bail N d) (bail N d) S (Q S) (X S):=by unfold Q X; split; exact (E.coat _).1 (); exact Suite.free _
 have hr(U:Openc (More N) d) : beforePing E k U.val=∑ S:Sa N,X S U:=by rw [beforePing,dif_pos U.property]; apply sum_congr rfl; intro S _; unfold X; split <;> rfl
 have hg:=saw_line E p (mul_pos (by norm_num) h); rw [show 4*a/2=a+a from by ring] at hg
 have he (S:Sa N):0≤ledgerV (W S):=sum_nonneg fun i _=>sum_nonneg fun j _=> (E.coat _|>.1 ()).nonn i j
 have hu:tallyC a Q ≤ expiry (4*a) v:=by
    apply le_trans _ hg; apply sum_le_sum; intro S _; change _ * ledgerV (Q S) ≤ _ * ledgerV (W S); unfold Q; split
    · exact mul_le_mul_of_nonneg_right (rent_up (le_add_of_nonneg_right h.le) _) (he S)
    rw [show ledgerV (0:Toll (Single N))=0 from by simp [ledgerV],mul_zero]; exact mul_nonneg (rent_pos _ _).le (he S)
 have hk(S:Sa N)(t:o∉ S): Q S=0:=by unfold Q; split; exact p _ t; rfl
 refine ⟨⟨⟨X,Q,hx,hk,hu,hr⟩,X,Q,hx,(fun S g=>⟨Classical.not_not.mp (mt (hk S) g),Classical.not_not.mp fun v=> g (if_neg v)⟩),hu,hr⟩,Y,T,fun S=>?_,fun S g=>?_,?_,fun x=>?_⟩
 · unfold Y T; split; exact Suite.free _; exact (E.coat _).1 ()
 · unfold T; split; rfl; exact p _ g
 · apply le_trans _ (mul_le_mul_of_nonneg_left hg (Real.exp_pos _).le); unfold tallyC; rw [mul_sum]; apply sum_le_sum; intro S _; change _*ledgerV (T S) ≤ _*(_*ledgerV (W S)); unfold T; split
   · rw [show ledgerV (0:Toll (Single N))=0 from by simp [ledgerV],mul_zero]; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (rent_pos _ _).le (he S))
   next g => rw [←mul_assoc]; refine mul_le_mul_of_nonneg_right ?_ (he S); unfold Branch.rent; rw [←Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith [mul_le_mul_of_nonneg_left (show (k:ℝ)≤ S.card from Nat.cast_le.mpr (le_of_not_gt g)) h.le]
 rw [beyond,dif_pos x.property]; unfold sky retain; rw [←sum_sub_distrib]; apply sum_congr rfl; intro S _; unfold Y; split; exact sub_self _; simp [F]
lemma saw_recover (E:StageTree N d a v)(k:ℕ)(x:Openc (More N) d):
    beforePing E k x.val+beyond E k x.val=sky E x:=by rw [beforePing,beyond,dif_pos x.property,dif_pos x.property]; abel
end YM.CF.LitCurrent
