import YM.CF.Emu.Law
set_option autoImplicit false
noncomputable section
namespace YM.CF.Emu
open YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Kea Flare Rush Tulip Cube Fock SU Dial Thera
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open Pic Sods
variable {α:Type*}{s:ℕ→Side}{R:ℕ→ℝ}{N:Side}{j n:ℕ}{K b v c l r τ:ℝ}
abbrev Greek(n:Side):ℝ:=n.val
def Plot.pal (Q:Plot α R)(i:ℕ)(a:α):TagT:= (Q.z i a,Q.seat a)
lemma growG(h:Yard s R):∀ᶠ i in atTop,R i≤Greek (s i) ∧ 1≤ R i:=by
 filter_upwards [h.high.eventually (eventually_ge_atTop 1),h.water.eventually (gt_mem_nhds Real.pi_pos)] with i e u; refine ⟨?_,e⟩; let l:= pinch (s i); have he:0<l:=pinch_pos _; exact le_of_mul_le_mul_right ((le_of_lt u).trans_eq (payH (N:=s i))) he
lemma lungG(n:Side)(x:ℝ)(h:1≤ x)(p:x ≤Greek n): ‖gain x‖≤ Greek n^2:=by
 rw [gain,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)]; apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).1; rw [Real.sq_sqrt (by positivity),←pow_mul]; exact (pow_le_pow_left₀ (zero_le_one.trans h) p _).trans (pow_le_pow_right₀ (h.trans p) (by decide))
lemma sizeG(Q:Plot α R)(J:List α)(h:Yard s R): ∃ C:ℝ,0<C ∧∀ᶠ i in atTop,∀ a∈J, ((Laurent.size (Q.z i a)):ℝ) ≤ C*Greek (s i):=by
 have he(x:α):∃ C:ℝ,0<C ∧∀ᶠ i in atTop, (Laurent.size (Q.z i x):ℝ) ≤ C*Greek (s i):=by
    let A:=‖Q.atV x‖+1; have hp: 0<A:=by unfold A; positivity
    refine ⟨4*A,by positivity,?_⟩; filter_upwards [(Q.voyage x).norm.eventually (gt_mem_nhds (show ‖Q.atV x‖<A from lt_add_one _)),growG h] with i t g; unfold Laurent.size; push_cast; have hr:= h.pos i; -- inspect
    refine (sum_le_sum (g:=fun _=> A*Greek (s i)) ?_).trans_eq ?_
    · intro a _; let V:=Q.z i x; apply le_trans _ (mul_le_mul_of_nonneg_left g.1 hp.le); -- inspect
      have he:= (sed (riseX (R i) V) a).trans (le_of_lt t); change |(V a:ℝ)/R i| ≤_ at he; rw [abs_div,abs_of_pos hr,div_le_iff₀ hr] at he; simpa using he
    simp; ring
 induction J with
 | nil=> exact ⟨1,one_pos, Eventually.of_forall fun _=>by simp⟩
 | cons a b ih=> obtain ⟨c,hc,C⟩:= ih; obtain ⟨d,v,G⟩:= he a; refine ⟨max d c,lt_max_of_lt_left v,?_⟩; filter_upwards [C,G] with i u w; intro j g; have hg:0<Greek (s i):= nPos _; rcases List.mem_cons.mp g with rfl|r; exact w.trans (mul_le_mul_of_nonneg_right (le_max_left ..) hg.le); exact (u _ r).trans (mul_le_mul_of_nonneg_right (le_max_right ..) hg.le)
lemma kem {d:ℝ}{p q:Wave (Single N)}{A: FC (Single N)}(h:Yep K p q d)(u:Pays K A b)(g:0 ≤d): ‖inner ℂ p (acts A q)‖≤ b*d:= Yep.lim (u.2 _ _ _ g h)
lemma paid_g (o:Site N)(U:Bkg (More N))(t:E)(R:ℝ)(a:α→TagT)(J:List α)(p:0<K)(h:‖gain R‖≤ Greek N^2):Pays (K*Greek N) (zoneA o U t R a J) (K^J.length * Greek N^(3*J.length)):=by
 let n:= Greek N; have hp:0<n:=nPos _; let F(x):= nac o U t R (a x)
 have hy : (K*n*n^2)^J.length= K^J.length*n^(3*J.length):=by rw [pow_mul, ← mul_pow]; congr 1; ring
 change Pays (K*n) (Emu.train F J) _; have he:=cash_f F J (fun i _=> (flo ..).trans_le (show ‖gain R‖≤n^2 from h)) (mul_pos p hp).le; rw [hy] at he; exact he
lemma proveV (o:Site N)(U V:Bkg (More N))(s:E)(R:ℝ)(x:TagT): (nac o U s R x).1=(nac o V s R x).1:=by dsimp only [nac]
lemma paid_v (o:Site N)(U V:Bkg (More N))(t:E)(R:ℝ)(a:α→TagT)(J:List α)(p:0<K)(h:∀ X:Bkg (More N), X=U∨X=V→∀ i∈J, ‖(nac o X t R (a i)).2‖≤ Greek N^2)(T b:ℝ)(l:∀ i∈J,‖(nac o U t R (a i)).2-(nac o V t R (a i)).2‖≤ Greek N^2*(T*Greek N*b)):Pays (K*Greek N) (zoneA o U t R a J-zoneA o V t R a J) ((J.length*K^J.length*T)*Greek N^(3*J.length+1)*b):=by
 let n:= Greek N; have hp:=nPos N; have hy : J.length*(K*n*n^2)^J.length*(T*n*b)=(J.length*K^J.length*T)* n^(3*J.length+1)*b:=by ring
 have hx:= cash_t (fun i=>nac o U t R (a i)) (fun i=>nac o V t R (a i)) (fun i=>proveV o U V t R (a i)) J (h U (Or.inl rfl)) (h V (Or.inr rfl)) l (mul_pos p (show 0<n from hp)).le; rw [hy] at hx; exact hx
lemma pay_v (Q:Plot α R)(J:List α)(h:Yard s R)(p:0<K):∃ C:ℝ,0<C∧ ∀ᶠ i in atTop,∀ (o:Site (s i))(U V:Bkg (More (s i)))(t:E), let n:=Greek (s i); let x:=zoneA o U t (R i) (Q.pal i) J; let y:=zoneA o V t (R i) (Q.pal i) J; Pays (K*n) x (C*n^(3*J.length)) ∧ ∀ z:ℝ,0≤z→ lawnK U V z→ Pays (K*n) (x-y) (C*n^(3*J.length+1)*z):=by
 obtain ⟨v,g,G⟩:=sizeG Q J h; obtain ⟨b,t,P⟩:=out_t
 let A:=b*v; let V:= K^J.length; let D:= J.length*V*A; let W:=max V D; have hv: 0<V:= pow_pos p _
 refine ⟨W,lt_max_of_lt_left hv,?_⟩; filter_upwards [G,growG h] with i u e; intro o U Y l n x y
 let F(X:Bkg (More (s i))) (j:α):= nac o X l (R i) (Q.pal i j); have hp:0<n:= nPos _; have hh := (mul_pos p hp).le; have hg := lungG (s i) (R i) e.2 e.1; have ht(X j): ‖(F X j).2‖ ≤ n^2:= (flo ..).trans_le hg
 constructor
 · have he:Pays (K*n) x (V*n^(3*J.length)):= paid_g o U l (R i) (Q.pal i) J p hg; exact he.weigh (mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity)) hh
 intro z l' S; have hl(a)(g:a∈J) : ‖(F U a).2-(F Y a).2‖ ≤ n^2*(b*v*n*z):=by
    refine (P S l' o l (R i) (Q.pal i a)).trans (mul_le_mul hg ?_ (mul_nonneg (mul_nonneg l' t.le) (Nat.cast_nonneg _)) (sq_nonneg _)); exact (mul_le_mul_of_nonneg_left (u a g) (mul_nonneg l' t.le)).trans_eq (by change z*b*(v*n)=_; ring)
 have he:Pays (K*n) (x-y) (D*n^(3*J.length+1)*z):= paid_v o U Y l (R i) (Q.pal i) J p (fun X _ i _=> ht ..) A z hl; exact he.weigh (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity)) l') hh
lemma bon{X X':Wave (Single N)}(p:0≤b)(h: Yep K (mateK N) (X-X') b)(V:Bkg (More N))(o: Site N)(t:E)(R:ℝ)(T:α→TagT)(J:List α)(q:Pays K (zoneA o V t R T J) c)(d:ℂ):‖wall o V t R T J X d-wall o V t R T J X' d‖≤ (c+‖d‖)*b:=by
 unfold wall matchF; let A:=zoneA o V t R T J; let u:=mateK N; have he: inner ℂ u (acts A X)-inner ℂ u X*d-(inner ℂ u (acts A X')-inner ℂ u X'*d)=inner ℂ u (acts A (X-X'))-inner ℂ u (X-X')*d:=by rw [map_sub]; simp only [inner_sub_right,sub_mul]; abel
 rw [he]; refine (norm_sub_le ..).trans ((add_le_add (kem h q p) (show ‖inner ℂ u (X-X')*d‖≤ ‖d‖*b by rw [norm_mul,mul_comm]; exact mul_le_mul_of_nonneg_left (Yep.lim h) (norm_nonneg _))).trans_eq ?_); ring
end YM.CF.Emu
