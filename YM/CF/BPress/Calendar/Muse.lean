import YM.CF.BPress.Calendar.Height
/-! Combined clock & size interface.
 Certified thresholds work for P,D with any desired cuff length before h.
 L_P,L_f,r_c,r_P,...,parameters.With PT acceptance. Cost bounds in `Cx^2` (can take common coefficient power `≈C` convention), **x in this file is y**.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Calendar
open Function NormedSpace Metric Finset MeasureTheory Filter Lattice RG Precision Pressure
open Cube Py Vale Vale.Grace Paige Scree Skye Fixed Dial Spire SU Wilson
open Net Hazel Chrono Sugar Lilac Grid Mount Recital Habitat Driver Meadow Meadow.Tent Meadow.Frame Meadow.Stamps Locale
open Wealth Weave Port Honey Before Between Recipe RG.PathData Branch LocalH Next.SectorChange Peel Spine Mosaic Engine Manna Huon
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace
attribute [local instance] Gauge.frobInner
variable {m s B:Side} {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
  {V: Grace K R L} {d x h p c:ℝ} {U:Grasp V.U B d}{W:GivenX V U} {Mstar:Side} {J:Robes Mstar V W}
variable {P:Before V p}{X:P.Between d J.n} {f: Angel X}{E:Earning X}
open Around Currencies -- namespace actual drop
structure Time (G:Around.Curb f E)(C x:ℝ):Prop where
 stamp : Magnate G x
 e :1≤ x
 u: payρ E f x ≤ C*x^2
 o : ∀ (m B:Side) (A:Bands (More (mid m B)) (era X x))(T:GramM (mid m B))(i:A.Index)(R':Recipe (A:=A) T),T.funds=K.top.clip→R'.C=K.top.paths→T.beta∈ Set.Icc (x/2) (2*x)→ 25* quoteN (y:=x) A i * cashmark R' (f.k x) (value E) (Between.stipend E x) i ≤ Real.exp (C*x^2*((More (mid m B)).val:ℝ)^3)
 p : 1≤ X.toGapSize.rP x∧ (era X x).P=X.toGapSize.rawP x
 bits : (temp x)⁻¹^2 ≤ X.toGapSize.rawP x ∧ (X.toGapSize.rawP x:ℝ) < 2*(temp x)⁻¹^2
 wing : f.F/Real.sqrt (temp x) ≤ ((frameWidth f.F x).val:ℝ) ∧ ((frameWidth f.F x).val:ℝ) < 2*(f.F/Real.sqrt (temp x))
structure Day (E:Earning X) where
 angel: Angel X
 curb: Curb angel E
 gain:ℝ
 gold: 2≤gain
 time: ∀ᶠ i:ℝ in atTop, Time curb gain i
lemma empire (E:Earning X)(v:LocalRatio L): Nonempty (Day E) :=by
 obtain ⟨f⟩:= Angel.angel X v; obtain ⟨G⟩:= curb f E; obtain ⟨a,p,g⟩:= paysH E (f:=f); obtain ⟨b,h,t⟩:= logHead E (f:=f); let c:= max 2 (max a b); refine ⟨⟨f,G,c,le_max_left ..,?_⟩⟩; filter_upwards [g,t,X.toGapSize.bounds,X.toGapSize.tail_P,magnate G, frame_bounds (zero_lt_one.trans_le f.oneF),eventually_ge_atTop (1:ℝ)] with x g t l u p w e; refine ⟨p,e,g.trans (mul_le_mul_of_nonneg_right ((le_max_left ..).trans (le_max_right ..)) (sq_nonneg _)),fun m B A v i V H K D=>(t m B A v i V H K D).trans ?_,⟨l.1,u⟩,l.2,w⟩; gcongr; exact (le_max_right a b).trans (le_max_right ..) -- tune binder
namespace Day
variable (D:Day E) {N:Side}
-- actual size and divisibility. on top of history.
structure Appear (x:ℝ)(A:Bands (More N) (era X x)):Prop where
 angle : Dyadic X.toGapSize D.angel.F x A
 grid : Meadow.Record P.tone (More N)
 grid' : Meadow.Record P.tone' (More N)
 mint : (D.curb.width x).val ∣ (More N).val
 size : max X.n X.age ≤ N.val
namespace Appear
lemma portProof {s v: Side}(a:v.val∣ s.val):∃ R:Locale.Hangar s,R.L=v:=by
 obtain ⟨n,c⟩:=a; refine ⟨⟨v,⟨n, Nat.pos_iff_ne_zero.mpr (fun g=> Nat.ne_of_gt s.property ?_)⟩,c⟩,rfl⟩; rw [g,mul_zero] at c; exact c
abbrev Q {A:Bands (More N) (era X x)} (h:Appear D x A): Locale.Hangar (More N) := (portProof h.mint).choose
lemma age {A:Bands (More N) (era X x)} (h:Appear D x A): (Q D h).L=D.curb.width x:= (portProof h.mint).choose_spec
end Appear
-- clarify can increase multiple on M, not just s? earlier periods P imposes only ∣s. need for common periods etc not asked here? state both later
lemma parade {j:ℕ}{p' : ℝ}{N0:ℕ}{U':Month p' 1 6 2 N0 V W}(t:Time D.curb D.gain x)(k:ℕ)(Q:Side) : ∃ M:Side,k≤M.val∧ Admit V N0 J U' M ∧ Q.val∣ (More (cell (M*Mstar) B R.L j)).val ∧ ∃ A:Bands (More (cell (M*Mstar) B R.L j)) (era X x),Appear D x A := by
 let u:=P.tone; let v:=P.tone'; let t':=D.curb.width x; let nB:=2*max X.n X.age+u.val+v.val+1; let V':=Q*(t'*(u*v)); obtain ⟨M,b,g,mk,z,e,a⟩:= periods (L':=D.angel.F) (X:=U') (J:=J) (j:=j) t.p.1 t.p.2 k nB V'; let N:= cell (M*Mstar) B R.L j; let Y:=More N; refine ⟨M,b,g,?_,e,⟨a,?_,?_,?_,?_⟩⟩; · exact dvd_trans (dvd_mul_right ..) z
 have hv:(u*v).val∣ Y.val:= dvd_trans (dvd_trans (show (u*v).val∣(t'*(u*v)).val from dvd_mul_left ..) (show (t'*(u*v)).val ∣ V'.val from dvd_mul_left ..)) z; exact ⟨dvd_trans (dvd_mul_right (α:=ℕ) ..) hv,(Nat.lt_succ_self u.val).trans_le (le_trans (b:=nB) (by unfold nB; omega) mk)⟩ -- syntax
 refine ⟨dvd_trans ?_ z,(Nat.lt_succ_self v.val).trans_le (le_trans (b:=nB) (by unfold nB; omega) mk)⟩; exact dvd_trans (show v.val∣(u*v).val from dvd_mul_left ..) (dvd_trans (dvd_mul_left ..) (show (t'*(u*v)).val ∣ V'.val from dvd_mul_left ..)) -- tune
 exact dvd_trans (dvd_trans (show t'.val∣(t'*(u*v)).val from dvd_mul_right ..) (show (t'*(u*v)).val ∣ V'.val from dvd_mul_left ..)) z
 change nB ≤ N.val*2 at mk; unfold nB at *; change max X.n X.age≤ N.val; omega
end Day
end YM.CF.BPress.Calendar
