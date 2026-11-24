import YM.CF.Emu.Fez
set_option autoImplicit false
noncomputable section
namespace YM.CF.Emu
open YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Kea Flare Rush Tulip Cube Fock SU Dial Thera
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open YM.Stationary (Gaia)
variable {N:Side}{j:ℕ}{M:Jill.Male}{C r D:ℝ}{d:Candle}
abbrev TagT:= Cover × Wing
def gain(R:ℝ):ℂ:= (Real.sqrt (R^3):ℝ)
def nac(o:Site N)(U:Bkg (More N))(t:E)(R:ℝ)(a:TagT):Reader0 (Single N) := let b:= signW a.2; let x:=gain R • hint o a.1 a.2 U t; (b,if b then -x else x)
lemma nac_k(o:Site N)(U:Bkg (More N))(t:E)(R:ℝ)(a:TagT):KeyT (nac o U t R a) (tickA N):=by
 unfold KeyT nac; dsimp only; split_ifs with g; rw [map_neg,map_smul,hinge,if_pos g,smul_zero,neg_zero]; rw [map_smul,hinge,if_neg g]
lemma cat(a b:Wing)(x y:Cover)(t:E)(U:Bkg (More N))(o:Site N)(R:ℝ)(g:0≤R)(P:Op (Single N)):rankG P (nac o U t R (x,a)) (nac o U t R (y,b)) = if signW a = signW b then 0 else if signW a then hopF o x y a b U t P R else -(hopF o y x b a U t P R):=by
 have ht: star (gain R)*gain R=(R:ℂ)^3:=by unfold gain; norm_cast; rw [show star (↑(Real.sqrt (R^3)):ℂ)=(↑(Real.sqrt (R^3)):ℂ) by simp,←sq, ←Complex.ofReal_pow,Real.sq_sqrt (by positivity)] -- tune
 unfold rankG nac; dsimp only; cases u:signW a<;> cases v:signW b<;> simp only [ite_true,Bool.false_eq_true,Bool.true_eq_false,ite_false,map_smul,map_neg,inner_smul_left,inner_smul_right,inner_neg_left,inner_neg_right,neg_neg,mul_neg,←mul_assoc]<;> rw [show gain R*(starRingEnd ℂ) (gain R)= (R:ℂ)^3 from (mul_comm ..).trans ht]<;> try simp [hopF]

lemma face_z (R:ℝ)(x y:Cover): riseX R x-riseX R y= riseX R (x-y):=by ext i; change ((x i:ℝ)/R)-( (y i:ℝ)/R)=((x i-y i:ℤ):ℝ)/R; rw [Int.cast_sub,sub_div]
variable {α:Type*}
structure Plot (α:Type*)(R:ℕ→ℝ) where
 z:ℕ→α→ Cover
 seat:α→Wing
 atV:α→Gaia
 voyage(x:α): Tendsto (fun i=>riseX (R i) (z i x)) atTop (𝓝 (atV x))
 port(i j:α): atV i=atV j→∀ᶠ k in atTop,z k i=z k j -- exact.
variable {s:ℕ→Side}{R:ℕ→ℝ}
namespace Plot
variable {m:ℕ}
def tag(Q:Plot α R)(o:Site (s m))(U:Bkg (More (s m)))(t:E)(i:α):= nac o U t (R m) (Q.z m i,Q.seat i)
def rho(Q: Plot α R)(i j:α):ℂ:= let a:=Q.seat i; let b:=Q.seat j; let x:=Q.atV i-Q.atV j; if signW a=signW b then 0 else if signW a then frank a b x else -(frank b a (-x))
lemma sun(Q:Plot α R){d:ℕ→Candle}(S:∀ i,Slide (s i) (d i))(W:ℕ→Jill.Male)(F:∀ i,Stag (s i)→ Peb)(o:∀ i,Site (s i))(k:Yard s R)(p:0<r)(g:0<C)(A:∀ x:Slot,∀ᶠ i in atTop, FormU ((S i).u x) j (W i) r C (trackF (S i) (F i) x))(h:1 ≤ j)(T:ℕ→E) (l:List α) : let K i x:= Q.tag (o i) (Kea.tax (d i)) (T i) x; Tendsto (fun i=>runes (fun x y=> rankG (Dofu _ (F i)) (K i x) (K i y)) l) atTop (𝓝 (runes Q.rho l)):=by
 intro K; apply offer_v; intro x y
 let a:=Q.atV
 have he(x y:α): Tendsto (fun i=>hopF (o i) (Q.z i x) (Q.z i y) (Q.seat x) (Q.seat y) (Kea.tax (d i)) (T i) (Dofu _ (F i)) (R i)) atTop (𝓝 (frank (Q.seat x) (Q.seat y) (a x-a y))):=by
    apply tally S W F o k p g A _ _ _ _ (a x-a y) _ _ h T
    · by_cases g:a x=a y; exact Or.inr ⟨sub_eq_zero.mpr g,Q.port x y g⟩; exact Or.inl (sub_ne_zero.mpr g)
    simpa only [←face_z] using Q.voyage x |>.sub (Q.voyage y)
 unfold K tag; simp_rw [show ∀ i,rankG (Dofu (s i) (F i)) (nac (o i) _ _ (R i) (Q.z i x,Q.seat x)) (nac _ _ _ _ (Q.z i y,Q.seat y))= _ from fun i=> cat _ _ _ _ (T i) (Kea.tax (d i)) _ _ (k.pos i).le _]; simp only [rho]; split_ifs with h u
 · exact tendsto_const_nhds (x:= (0:ℂ))
 · exact he x y
 rw [neg_sub]; exact (he y x).neg
end Plot
end YM.CF.Emu
