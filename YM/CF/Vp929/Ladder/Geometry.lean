import YM.CF.Vp929.Stage.Compare

/-! Compatible mesh reindexing, including appending Last, roof, and test frequency data. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief VolumeRate
open scoped Mew
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
variable {d : ℝ} {m m' n n' N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
  {h x x' delay : ℝ} {C D R0 : ℝ → ℝ} {N0 k k' : ℕ} {P : Prescription R B}

section mesh
variable (m m' B : Side) (n k : ℕ)
lemma mesh_sum : mesh m B (n+k)=mesh (mesh m B n) B k := by unfold Vale.mesh; rw [pow_add,mul_assoc]
lemma mesh_up : mesh m B (n+1)=mesh (m*B) B n := by rw [add_comm,mesh_sum]; simp [Vale.mesh]
abbrev volumeBase (m B : Side) : ℝ := sites (Scree.mid m B)
lemma sites_step : sites (cell m B m' (n+1))= sites (cell m B m' n)*(m'.val:ℝ)^4 := by rw [sites,grows,sites]; simp only [More,PNat.mul_coe]; push_cast; ring
lemma sites_zero : sites (cell m B m' 0)= volumeBase m B := by unfold volumeBase cell; congr; simp [Vale.mesh]
lemma mesh_ge : m.val ≤ (mesh m B k).val := Nat.le_mul_of_pos_right _ (B^k).property
lemma mesh_ge' : m.val ≤ (mesh (m*N) B k).val := le_trans (Nat.le_mul_of_pos_right _ N.property) (mesh_ge (m*N) B k)
lemma ge60 (p : 61 ≤ m.val) : 60 < (More (cell m B m' n)).val := by have h:= p.trans (amplit m B m' n); change _ < (cell m B m' n).val *2; omega
end mesh
namespace Under
lemma move {A : Spine W m k} {A' : Spine W m' k'} {l : ℕ} (p : Under A A' l)
    (i) (hi : i<k) : A.last.move i=A'.last.move (i+l) := by
  unfold Gold.Last.move; rw [p.fee i hi,show k-1-i=k'-1-(i+l) by have := p.height; omega]
lemma pilot {A : Spine W m k} {A' : Spine W m' k'} {l : ℕ} (p : Under A A' l) (x x' : ℝ)
    (i) (hi : i ≤ k) : A'.pilot x' (i+l)-A.pilot x i=A'.pilot x' l-x := by
  induction i with
  | zero=> rw [Nat.zero_add,A.pilot_zero]
  | succ i ih=>
    have hx:= p.move i hi; have := A.pilot_move (x:=x) i; have h:= A'.pilot_move (x:=x') (i+l); have he:= ih (by omega); rw [show i+1+l=i+l+1 by omega]; linarith
end Under

/-- Rung at exponent `k` of geometric period ladder. `m` here is A0. -/
abbrev rung (R : Patch) (m : Side) (k : ℕ) := mesh m R.L k
/-- Common q at level `n`; at all negative levels, q at level zero. -/
def commonQ (R : Patch) (B m : Side) (n : ℕ) := Real.pi / (mid m B).val / (R.L.val:ℝ)^n
lemma commonFreq {m k n n' B} (p : commonQ R B m 0 ≤ Real.exp (- (R.L.val:ℝ))) (hv : n' ≤ n) :
    Frequency R.L (cell (rung R m k) B R.L n) (commonQ R B m n') := by
  let H:=k+n-n'; let L:=R.L; let A:=cell (rung R m k) B R.L n; let s₀:=mid m B; let l:ℝ:=L.val
  have hL : 1 ≤ l := by unfold l; exact_mod_cast L.property
  have h:l≠ 0:= ne_of_gt (zero_lt_one.trans_le hL); have hA:= A.property; have hs:s₀.val ≠ 0 := s₀.property.ne'
  let q:= commonQ R B m n'; have he: (A.val:ℝ) = s₀.val * l^(k+n) := by
    change ((( (m.val* (L^k).val)*(L^n).val*2*B.val: ℕ)):ℝ)= ((m.val*2*B.val:ℕ):ℝ)*_
    unfold l; push_cast; ring
  have E : q=L.val^H*(Real.pi/A.val) := by
    rw [he,show k+n = H+n' by unfold H; omega,pow_add]
    change Real.pi/s₀.val/l^n'=l^H*(Real.pi/ _); field_simp
  have eh:=Real.pi_pos; have hl : 0<l := zero_lt_one.trans_le hL
  refine ⟨?_,le_trans (b:= commonQ R B m 0) ?_ p,⟨(L.val)^H,?_⟩,⟨(L.val)^H, R.odd_side.pow,?_⟩⟩
  · change 0 < q; rw [E]; positivity
  · unfold commonQ; rw [pow_zero,div_one]; apply div_le_self _ (one_le_pow₀ hL); positivity
  · rw [Nat.cast_pow]; change q = _ * (2*Real.pi/ ((A.val*2:ℕ):ℝ)); rw [E]; push_cast; ring
  rw [Nat.cast_pow]; exact E

-- Transport-dependent pieces; the Ratio at either cite has count R.L.
private def renew {E : Side → Sort*} (u : n=m) (v : E m) : E n := u.symm ▸ v
private lemma eq_renew {E : Side → Sort*} (u : n=m) (v : E m) : HEq (renew u v) v := by subst m; rfl
private lemma transport_mint {a c lag : ℕ} (u : Vale.mesh m R.L a = Vale.mesh m' R.L c)
    (v : Vale.mesh m R.L (a+1)=Vale.mesh m' R.L (c+1)) {I₀ I₁ I₀' I₁' f} (e : HEq I₀ I₀') (e' : HEq I₁ I₁') (p : V.L.ticket m' U W.C lag c I₀' I₁' f) : V.L.ticket m U W.C lag a I₀ I₁ f := by
  have H : ∀ {m m' n n' : Side} {I₀ : Interest (mid m B)} {I₁ : Interest (mid n B)} {I₀' : Interest (mid m' B)} {I₁' : Interest (mid n' B)} e' e e₁ e₁', m=m' → n=n' → HEq I₀ I₀' → HEq I₁ I₁' → Mint (A:=n') (m:=m') U W.C f K I₁' I₀' ⟨R.L,e'⟩ (V.L.op lag e₁') (V.L.path lag) (V.L.path (lag+1)) → Mint U W.C f K I₁ I₀ ⟨R.L,e⟩ (V.L.op lag e₁) (V.L.path lag) (V.L.path (lag+1)) := by
    rintro m _ n _ w i w' i' s t U Q rfl rfl v v₁ h; rw [heq_eq_eq] at *; subst w' i'; exact h
  exact H _ _ _ _ u v e e' p

lemma extend_last (A : V.L.Last U W.C m k) (hp : m=m'*R.L) (pC : W.C.i ≤ m'.val) :
    ∃ A' : V.L.Last U W.C m' (k+1), (∀ i : ℕ, HEq (A.Q i) (A'.Q (i+1))) ∧ ∀ i : ℕ, A.shift i=A'.shift (i+1) := by
  subst m; have H (i) : Vale.mesh m' R.L (i+1)=Vale.mesh (m'*R.L) R.L i := mesh_up m' R.L i
  let f(i): Interest (cell m' B R.L (i+1)):= renew (E:=fun x=> Interest (mid x B)) (H i) (A.Q i); have e(i):HEq (f i) (A.Q i):=eq_renew ..
  have hp(i):InterestX W.C _ (f i):=by
    apply (show ∀ {n m : Side} (e : n=m) (i : Interest (mid m B)), InterestX W.C _ i → InterestX W.C _ (renew (E:=fun n=> Interest (mid n B)) e i) from fun {n m} e => by subst m; exact fun _ h=> h) (H i) (A.Q i) (A.sound i)
  obtain ⟨w,v,h⟩:= V.L.earnest W.paid 0 k (pC.trans (amplit m' B R.L 0)) (f 0) (hp 0)
  let Q : (i:ℕ) → Interest (cell m' B R.L i):= fun i=> Nat.casesOn i w f; refine ⟨⟨Q,fun i=> Nat.casesOn i v A.shift,?_,?_,?_⟩,fun i => (e i).symm,fun i=> rfl⟩
  · change renew _ _ = _; rw [A.top]; exact (show ∀ {n m: Side} (e:n=m), renew (E:=fun n=> Interest (mid n B)) e (vanilla _) = vanilla _ from fun {n m} e=> by subst m; rfl) _
  · rintro (_|n); exact h.courage; exact hp n
  rintro (_|n) u
  · rw [show k+1-1-0=k by omega]; exact h
  rw [show k+1-1-(n+1)=k-1-n by omega]; exact transport_mint (H n) (H (n+1)) (e n) (e _) (A.pass n (by omega))

/-- prepend the rack entry Loom and preserve the rest of Cape from original choice. -/
lemma extend_under (A : Spine W m k) {T : Month x 1 6 2 N0 V W} (c : A.Can J q T)
    (hp : m=m'*R.L) (pC : W.C.i ≤ m'.val) {w : ℝ} (hw : Frequency R.L (cell m' B R.L 0) w) (s : Scree.Loom (cell m' B R.L 0))
    (hs : RocketV V (mesh m' R.L 0) (mesh m' R.L 1) U W J s (apt m' B R.L 0) q)
    (u : T.q ≤ m'.val) (v : 61 ≤ m'.val) :
    ∃ A' : Spine W m' (k+1), Under A A' 1 ∧ A'.freq 0=w ∧ A'.Can J q T := by
  subst m; have H (i) : Vale.mesh m' R.L (i+1)=Vale.mesh (m'*R.L) R.L i := mesh_up m' R.L i
  obtain ⟨A',p,p'⟩:= extend_last A.last rfl pC
  let Y (i) := renew (E:=fun n=> Scree.Loom (mid n B)) (H i) (A.loom i)
  let D : Spine W m' (k+1):= ⟨A',fun i=> Nat.casesOn i s Y, fun i=> Nat.casesOn i w A.freq⟩
  refine ⟨D, ⟨rfl,fun i=> (H i).symm,p,fun i=> (eq_renew (E:=fun n=>Scree.Loom (mid n B)) (H i) _).symm,fun i _=> p' i,fun _ _=> rfl⟩,rfl, ⟨u,v,?_,?_,c.pole,c.isle⟩⟩
  · rintro (_|i); exact hs; change RocketV _ _ _ _ _ _ (Y i) _ _
    exact (show ∀ {m m' n n' : Side} (h:m=m') (t:n=n') (Y : Scree.Loom (mid m' B)) s' s,
              RocketV V m' n' U W J Y ⟨R.L,s'⟩ q → RocketV V m n U W J (renew (E:=fun m=> Scree.Loom (mid m B)) h Y) ⟨R.L,s⟩ q from fun {m m' n n'} p q=> by subst m'; subst n'; exact fun _ _ _ h=> h) (H i) (H (i+1)) _ _ _ (c.cape i)
  rintro (_|i); exact hw
  change Frequency R.L (mid _ B) (A.freq i); rw [H]; exact c.frequencies _
end YM.CF.Py.Rate
