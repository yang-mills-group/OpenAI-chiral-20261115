import YM.SU5.Reconstruction.Trap.Pilot
/-!
# Observer entanglement of unit directions k spectra, thus joint
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Picket
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
open Real
open YM.Multiplier Chirp CrossedFrame OS Semigroup Boundary Probe
variable {H D K:Hilbert} {a b : Axis} (r:b≠a) (S:OS.Semigroup H a) (Q:OS.Semigroup D b) (C:Clasp K H D)
noncomputable def boost (u:ℝ):= C.cLeft (-u/Real.pi)
lemma boost_thru (x:ℝ)(y:ℝ) : boost C x * boost C y=boost C (x+y):= by unfold boost; rw [C.groupLeft]; congr 1; ring
lemma boost_first : boost C 0=1:= by simpa [boost] using (C.left_credentials 0).1
lemma boost_pays (x:ℝ): Pays (boost C x) := (C.left_credentials _).2.2
lemma warm (x:H): Continuous (fun t=> boost C t x) := C.scheduleLeft x|>.comp (show Continuous fun t:ℝ=> -t/π by fun_prop)
abbrev Behind : Prop:=∀ x:E4, x a=0→ x b=0→C.Pass (trans S x) (trans Q x)
variable (p:Paces b S)(q:Paces a Q) (δ:Beam r S Q C)(G:Behind S Q C)
lemma trans_sum (S:OS.Semigroup H a)(x y:E4) : trans S (x+y)=trans S x*trans S y:= (S.unit.sends ..).symm
lemma trans_star (x:E4): star (trans S x) = trans S (-x):= by
 have hh:trans S x * trans S (-x)=1:= by rw [← trans_sum,add_neg_cancel]; exact S.unit.origin
 exact left_inv_eq_right_inv (mobile S x).1 hh -- perhaps need no cancellative
local notation "V"=> C.look.toContinuousLinearEquiv.toContinuousLinearMap
local notation "F"=> trans S
local notation "T"=> trans Q
include G
lemma noCost {x:E4}(g:x a=0)(h:x b=0): C.ScalePass 0 0 (trans S x) (trans Q x) 1 := by
 refine ⟨IsStarProjection.zero _,IsStarProjection.zero _,?_,zero_lt_one,mobile ..,mobile ..,Commute.zero_right _,Commute.zero_right _,?_,?_⟩ -- maybe arguments
 · exact (by simpa using (C.one.sub C.one))
 · rw [Mint.at_base,mul_one]; exact G x g h
 rw [inv_one,Mint.at_base,one_mul, trans_star, trans_star]; exact G _ (by simp [g]) (by simp [h])
lemma lookLee {x:E4}(g:x a=0)(h:x b=0): (V).comp (F x)=(T x).comp V:= by
 let z:=C.halfway (noCost S Q C G g h); have he:= C.halftime (noCost S Q C G g h); ext1 x'; obtain ⟨p,rfl⟩:=C.Left.surjective x'
 change C.Right (C.Left.symm (F x (C.Left p)))= T x (C.Right (C.Left.symm (C.Left p)))
 rw [show F x (C.Left p)=C.Left (z p) from DFunLike.congr_fun he.1.symm p,LinearIsometryEquiv.symm_apply_apply,LinearIsometryEquiv.symm_apply_apply]; exact DFunLike.congr_fun he.2 p
lemma boostLee (u:ℝ) {x:E4}(g:x a=0)(h:x b=0): Commute (boost C u) (trans S x):=by
 let s:= -u/π; let f:=F x; have ht:C.cLeft s * F x * star (C.cLeft s) = F x:=by simpa using C.passage (noCost S Q C G g h) s
 rw [commute_iff_eq]; nth_rw 2 [←ht]; change _=boost C u*f*star (boost C u)*_; rw [mul_assoc (boost C u * f), (boost_pays C u).1,mul_one] -- tune
omit G
include p q δ
local notation "P"=> S.ℚmeasure
local notation "Q₁"=> Q.ℚmeasure
variable (u:ℝ)
lemma look_ray (t:ℝ)(e:ℝ)(c:e=1∨e=-1): (V).comp (F (t • head a b e))=(T (t • head b a (-e))).comp V:= by
 have hm: -e=1∨ -e=-1 := by rcases c with c|c <;> rw [c] <;> simp
 rw [← shift b e t S p c, ←shift a (-e) t Q q hm]; exact C.frameInterlaces _ (ticket_cont ..|>.measurable) (Picket.positive b e) (ticket b a (-e)) (ticket_cont ..|>.measurable) (Picket.positive a (-e)) e c P Q₁ (crosses_at r S Q C e c p q δ) _ (pure t)
local notation "K₁" x:max=> boost C x
lemma boost_item (e t:ℝ)(c:e=1∨e=-1) : boost C u* trans S (t • head a b e)= trans S ((t*Real.exp (e*u)) • head a b e) * boost C u:= by
 let v:= -u/π; let h:= ticket a b e; let k:= Real.exp (e*u)
 have ht:Clasp.lengthen e v= Real.exp (e*u):= by unfold Clasp.lengthen v; rw [show -e*π*(-u/π)=e*u from by field_simp]
 rw [←shift b e _ S p c,← shift b e _ S p c]; have he: concern P h (t*k) = order P (sound t ∘ (fun x=> Clasp.lengthen e v*h x)):= by
   unfold concern; congr 1; rw [ht]; unfold k; funext x; unfold comp sound; push_cast; ring_nf
 change C.cLeft v * _= concern P h (t*k)* _; rw [he]; exact C.weightTransport (ticket a b e) (ticket_cont ..|>.measurable) (Picket.positive b e) (ticket b a (-e)) (ticket_cont ..|>.measurable) (Picket.positive a (-e)) e c P Q₁ (crosses_at r S Q C e c p q δ) _ (pure t) v
include G
lemma look_bill (x:E4) : (V).comp (trans S x)=(trans Q (quarter a b x)).comp V:= by
 have hm:= @look_ray _ _ _ _ _ r S Q C p q δ -- tune
 nth_rw 1 [← heft a b x]; unfold quarter; rw [trans_sum, trans_sum S, trans_sum,trans_sum Q]; ext1 z; -- simp and align. use comp identity
 let t1:= rise a b x 1; let t2:=rise a b x (-1); let y:=lee a b x; let F1:=F (t1 • head a b 1); let Jf:= T (t1 • head b a (-1)); let F2:=F (t2 • head a b (-1)); let J:=T (t2 • head b a 1); let M:=T y; let N:=F y
 have h1(v:H): (V) (F1 v)= Jf ((V) v):= DFunLike.congr_fun (hm t1 1 (by simp)) v
 have h2(v:H): (V) (F2 v)= J ((V) v):= by unfold F2 J; have hp:=hm t2 (-1) (by simp); rw [neg_neg] at hp; exact DFunLike.congr_fun hp v
 change (V) (F1 (F2 (N z)))= Jf (J (M ((V) z))); rw [h1,h2]; congr 2; exact DFunLike.congr_fun (lookLee S Q C G ((lees r x).1) ((lees r x).2)) z -- shadow Jf
lemma boost_bill (x:E4) : boost C u* trans S x=trans S (move a b u x)* boost C u:=by
 nth_rw 1 [← heft a b x]; unfold move; rw [trans_sum S,trans_sum S,trans_sum S,trans_sum S]; set k:=boost C u
 have he:= boost_item r S Q C p q δ u 1 (rise a b x 1) (by simp); have hp:= boost_item r S Q C p q δ u (-1) (rise a b x (-1)) (by simp); simp only [one_mul,neg_mul] at he hp; rw [← show boost C u=k from rfl]; rcases lees r x with ⟨v,h⟩
 rw [←mul_assoc,←mul_assoc,he,mul_assoc _ (boost C u), hp,mul_assoc, mul_assoc, mul_assoc, (boostLee S Q C G u v h).eq]; simp only [mul_assoc]
end YM.Picket
