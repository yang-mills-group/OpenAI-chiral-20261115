import YM.SU5.FiniteGaugeData.Poin.Twine
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Function Filter Metric Complex MeasureTheory Set OS OS.Semigroup
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {n:ℕ}{H:Hilbert}{a:Axis}(S:OS.Semigroup H a)(x y:H)
open Spectral Boundary Probe
lemma inspect {R:Type}[Monoid R]{G:Fin n→R}{F J:Bin n R}(p:∀ i j: Fin n,i<j→ F i j=J i j) : Rail G F= Rail G J:= by induction n with
 | zero=> rfl
 | succ n ih=>
    rw [Rail_step _ F,Rail_step _ J,ih (G:=Fin.tail G) (J:=rump J) (fun i j t=> p i.succ j.succ (Fin.succ_lt_succ_iff.mpr t))]; congr 2; cases n with | zero=> rfl | succ n=> rw [s1S,s1S]; exact p _ _ (Fin.succ_pos _)
private lemma rail_in (A:ℂ→Fin n→H.Op)(B:ℂ→ Bin n H.Op) (z:ℂ)(p:∀ i, AnalyticAt ℂ (fun z=>A z i) z)(h:∀ i j:Fin n,i<j→ AnalyticAt ℂ (fun z=> B z i j) z): AnalyticAt ℂ (fun z=> Rail (A z) (B z)) z:=by
 induction n with
 | zero=> exact analyticAt_const
 | succ n ih=>
    have he:AnalyticAt ℂ (fun z=>s1 n (B z)) z:=by cases n with | zero=> exact analyticAt_const | succ n=> simp_rw [s1S]; exact h _ _ (Fin.succ_pos _)
    simp_rw [Rail_step (n:=n)]; exact ((p 0).mul he).mul (ih (fun z=>Fin.tail (A z)) (fun z=>rump (B z)) (fun i=> p i.succ) (fun i j t=> h _ _ (Fin.succ_lt_succ_iff.mpr t)))
variable (Ω:H)(b:Cross a)(A:Shelf S b)(z w:Fin n→ℂ)(Y:Fin n→ Cross a) -- COORD
variable (G:Fin n→H.Op)(ν:Fin n→ℕ)
def Radial := ∀ i j : Fin n,i<j→ Wheel (z j-z i) (w j-w i)
def rise (i j:Fin n): H.Op:= foil S b A (ν i+ν j) (z j-z i) (w j-w i)
local notation "Φ"=> rise S b A
abbrev Draw (i j:Fin n):= rise S b A z w ν i j * S.U (Y j-Y i)
def Mell := inner ℂ Ω (Rail G (Draw S b A z w Y ν) Ω)
local notation "F"=> foil S b A
lemma mellA (r t:ℂ→Fin n→ℂ)(f:ℂ→Fin n→H.Op)(x:ℂ)(p:Radial (r x) (t x))(g:∀ i,AnalyticAt ℂ (fun x=>r x i) x)(h:∀ i,AnalyticAt ℂ (fun x=>t x i) x)(G:∀ i,AnalyticAt ℂ (fun x=> f x i) x): AnalyticAt ℂ (fun x=> Mell S Ω b A (r x) (t x) Y (f x) ν) x:=by
 let Z:= (innerSL ℂ Ω).comp (ContinuousLinearMap.apply ℂ H.space Ω); apply AnalyticAt.comp (Z.analyticAt _) (rail_in f (fun x=> Draw S b A (r x) (t x) Y ν) x G _)
 intro i j t'; have h:= hol_whole S b A (ν i+ν j) x (fun y=>r y j-r y i) (fun y=>t y j-t y i) ((g j).sub (g i)) ((h j).sub (h i)) (p i j t'); exact h.mul analyticAt_const
lemma riseLife (p:Radial z w): PaysL S (rise S b A z w ν) := ⟨fun i j h=>(holdsR S b A _ _ _ (p i j h)).symm⟩
lemma rise_g (Y Θ:ℕ→Fin n→ℂ) (t:∀ i, Radial (Y i) (Θ i))(q:∀ i,Tendsto (fun t=> Y t i) atTop (𝓝 0))(v:∀ i,Tendsto (fun t=>Θ t i) atTop (𝓝 0)): Solution S ν (fun t=> rise S b A (Y t) (Θ t) ν):=by
 refine ⟨fun i=>riseLife S b A _ _ _ (t i), fun i j u=> ?_⟩; let z(t:ℕ):=Y t j-Y t i; let w(t:ℕ):=Θ t j-Θ t i; simp_rw [Xpay,rise]; change Gesture (fun k=> F (ν i+ν j) (z k) (w k)* Cache S (ν i+ν j)); have he(k:ℕ):= aerial S b A _ _ (ν i+ν j) (t k i j u); unfold z w; simp_rw [he]; exact secure S b A z w (fun k=> t k i j u) (by simpa only [sub_self] using (q j).sub (q i)) (by simpa only [sub_self] using (v j).sub (v i))
#print axioms mellA
#print axioms rise_g
-- positional telescope. using Cross d.Add coords
variable (u v:Fin n→ℝ)(p:Radial z w)
def board (α β:ℝ)(y:Cross a): E4:= y.val + (β • b).val + α • basis a
abbrev shape (α β:Fin n →ℝ) (y:Fin n→ Cross a):= points fun i=> board b (α i) (β i) (y i)
local notation "∆" f:max i:max j:max=> f j-f i
lemma bclock (t u:ℝ)(y:Cross a): board b t u y a=t:=by unfold board; simp [ show y.val a=0 from y.property, show b.val a=0 from b.property] -- simp tsmul.val maybe
lemma bspace (t u:ℝ)(y:Cross a): SEP a (board b t u y)= y+u • b:=Subtype.ext (by change board b t u y-(board b t u y a) • basis a=y.val+_; rw [bclock,board,add_sub_cancel_right])
lemma bpay (t u:ℝ)(y:Cross a): M S (board b t u y)= S.edge t * S.U (u • b) * S.U y:=by
 change S.edge (board b t u y a)* (S.U _) =_; rw [bclock,bspace,add_comm y, S.space]; rw [mul_assoc]; rfl
-- temporal coords complex ζ after real adjustment
abbrev spill := fun i=> z i+sideways (u i)
abbrev spur := fun i=> w i+(u i:ℂ)
local notation "J"=>Φ z w ν -- Φ z w?
local notation "X" => shape b u v Y
lemma lift_t(i j:Fin n): spill z u j-spill z u i= z j-z i+sideways (u j-u i):=by unfold spill sideways; push_cast; ring
lemma lift_u(i j:Fin n): spur z u j-spur z u i= z j-z i+(↑(u j-u i):ℂ):=by unfold spur; push_cast; ring
lemma jetset (p:Radial z w): Radial (spill z u) (spur w v):=by intro i j h; have he:=p i j h; rw [lift_t,lift_u]; unfold Wheel Shelf₀; change |(w j-w i+(↑(v j-v i):ℂ)).im|<(z j-z i+sideways (u j-u i)).re; rw [Complex.add_im, ofReal_im, Complex.add_re,side,add_zero,add_zero]; exact he
lemma monument(i j:Fin n): (X) j - (X) i = board b (u j-u i) (v j-v i) (Y j-Y i):=by change board b _ _ _-board b _ _ _=_; unfold board; simp_rw [sub_smul]; simp only [Submodule.coe_sub]; abel -- type `_` problem
lemma upright(p:Radial z w)(i j:Fin n)(h:i<j): Draw S b A (spill z u) (spur w v) Y ν i j= (J i j)* M S ((X) j-(X) i) := by
 let k:=ν i+ν j; let w':=w j-w i; let z':=z j-z i; let t:=u j-u i; let v':= v j-v i; have he:=p i j h
 rw [monument, bpay]; unfold Draw rise; rw [lift_t, lift_u]; rw [hillside S b A (z j-z i + sideways (u j-u i)) w' k v' (show Wheel (z j-z i+sideways (u j-u i)) _ from (by show |w'.im|< (z j-z i+sideways (u j-u i)).re; unfold w'; simpa using (show _ from he))), rolling S b A _ _ _ t he]; unfold t; simp only [mul_assoc]; rfl -- h may `rw` fail w' notation.
#print axioms upright
variable (ω:∀ x:E4, M S x Ω=Ω)
include ω
lemma stunts (p:Radial z w): Mell S Ω b A (spill z u) (spur w v) Y G ν= inner ℂ Ω (pitch S G J X Ω):=by
 let Gq:=twists S Ω G J (X).ofLp ω (Each n); rw [show inner ℂ Ω (pitch S G J X Ω)=_ from Gq]; unfold Mell; congr 2; apply inspect; intro i j h; rw [upright _ _ _ _ _ _ _ _ _ p _ _ h]; let V:=M S; let A':=J i j; let B(i:Fin n):= X i; change A'*V (B j-B i)=V (-(B i))*A'* V (B j); have he: Commute (V (-B i)) A':=holds S b A _ _ _ (p i j h) (-B i); rw [he.eq,mul_assoc]; rw [tgo]; rw [add_comm,←sub_eq_add_neg] -- inspect G met on same.SΩ.Tune
#print axioms stunts
-- real Mean.H integral no spectrum used.Separate height
variable (x:Points n)
omit ω
def Chronos (x:Points n) : Prop := StrictMono (fun i=>x i a)
abbrev rho (ι:Fin n→ℝ) (i j:Fin n):= Par S (ν i+ν j) (ι j-ι i).toNNReal
def clockV (a:Axis)(x:Points n):= fun i=> x i a
def meanE (L:List (Fin n)):ℂ := inner ℂ Ω (Film (fun i=>coreSp S (x i) (G i)) (rho S ν (clockV a x)) L Ω)
lemma Vclock: clockV a (shape b u v Y)=u:= funext fun i=>bclock b (u i) (v i) (Y i)
abbrev TopG := meanE S Ω G ν x (Each n)
abbrev soaked(z:Fin n→ℝ): Fin n→ℂ:= fun i=> z i
lemma wet (u:Fin n→ ℝ) : Radial (soaked u) (soaked v) ↔ StrictMono u:= by unfold Radial Wheel Shelf₀ StrictMono; simp -- norm proof reduce
include ω
lemma meanR (e:StrictMono u): TopG S Ω G ν (shape b u v Y) = Mell S Ω b A (soaked u) (soaked v) Y G ν :=by
 let z': Fin n →ℂ :=soaked u; let w':Fin n→ℂ:=soaked v; let G':=rise S b A z' 0 ν; let x':Points n:=X; let y':=shape b 0 v Y
 have hi(i:Fin n): (SEP a (x' i)).val = y' i:=by rw [show SEP a (x' i)=_ from bspace b (u i) (v i) (Y i)]; change _=board b 0 (v i) (Y i); unfold board; simp
 have h:(0:Fin n→ ℂ)=soaked (fun _=> (0:ℝ)):=funext (fun i=>by simp [soaked]); have he:Radial (soaked u) 0:= by rw [h]; apply (wet _ _).mpr e -- cast synt
 have hp: Mell S Ω b A z' w' Y G ν=inner ℂ Ω (pitch S G G' y' Ω):=by
    have hz: spill z' 0=z' ∧ spur 0 v=w':= ⟨by funext i; simp [spill],by funext i; simp [spur,w',soaked]⟩
    exact hz.1 ▸ hz.2 ▸ stunts S Ω b A _ _ Y G ν 0 v ω he -- cast replacing definitions.Tune
 have hx(i j:Fin n)(p:i<j): G' i j = rho S ν u i j:=by
    let v:= z' j-z' i; have ht:0<v.re:= wheel_pos _ _ (he i j p); let Z:= (u j-u i).toNNReal; have hw:v= OS.Semigroup.duration Z:=by unfold v OS.Semigroup.duration Z z' soaked; rw [Real.coe_toNNReal _ (sub_nonneg.mpr (e p).le)]; push_cast; rfl
    have hz(t:ℝ):= realF S b A v (ν i+ν j) t ht; change foil S b _ _ v (0-0)=_; rw [sub_zero, ← Complex.ofReal_zero, hz,albe,zero_smul,S.uZero,hw]; rfl -- ht ∈. tune shadow
 change inner ℂ Ω (Rail (fun i=> optx S (G i) (SEP a (x' i)).val) (rho S ν (clockV a x')) Ω)=_; simp_rw [hi]; rw [show clockV a x'=u from Vclock .., ← inspect (G:=_) hx,hp]
#print axioms meanR
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
