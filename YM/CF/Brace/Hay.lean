import YM.CF.Brace.Flowers
/-! λ_b independent exactly, even sectors. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Brace
open Function Filter Lattice Metric Lat Finset Cube Tenant SU Fock Dial Phase
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {m B:Side}{j l b n:ℕ}{e p d a w:ℝ}{X Y:Sheen m B}{t:Cue m}{U:Skin m B}
def antler (j l n:ℕ)(M:Tulip.Male)(m B:Side)(U:Skin m B)(X:Sheen m B)(v:Cue m):= torque j l n M m B U (tailP m B X v) X (stick 1)
def hero (j l n:ℕ)(M:Tulip.Male)(m B:Side)(U:Skin m B)(X Y:Sheen m B)(t:Cue m):ℂ:= antler j l n M m B U X t-antler j l n M m B U Y t
lemma equal_ord (m B:Side) (U:Skin m B)(t v:ArrayF m)(r:Zone)(h:∀ i:Spot m,i.2∈r → t i=v i)(x:Sheen m B){q:Sq}(p:q∈zone r)(M:Tulip.Male): torque j l n M m B U t x q=torque j l n M m B U v x q:=by
 apply sum_congr rfl; intro i _; rw [facePay, facePay, ark_same m B U t v r h _ _ p, ark_same m B U t v r h _ _ p]
lemma att_dome {X:Sheen m B}{v:Cue m}(p:mantle m B U X v)(h:Guard U e)(k:Slow U (hook X) d): Foil m B e d {1} (tailP m B X v) X U:=⟨(by rw [show insert 0 ({1}:Zone)=insert 1 {0} from Finset.insert_comm 0 1 ∅]; exact p),fun i=>by simp [tailP,capRow,arrayZ], h,k,by simp⟩ -- unused s implicit!
variable (H:CoinG j l b n d a w)(G:Guide B e p d)(hm:b≤(CSide m B).val)
include H G hm
lemma atop {k:ℝ}{x:Sheen m B}(V:Cue m)(t:Cue m)(h:Attested m B U (capRow (tailP m B x V) 2 t) (insert 2 (insert 1 {0})))(p:Guard U e)(hx:Slow U (hook x) k): Foil m B e k {1,2} (capRow (tailP m B x V) 2 t) x U:= by
  have he : insert 0 ({1,2}: Zone)=insert 2 (insert 1 {0}):=by decide; -- tune
  exact ⟨he.symm ▸ h,fun i=>by simp [tailP,capRow,arrayZ],p,hx,by decide⟩
lemma shared (h:Guard U e)(v t:Cue m) (x y:Sheen m B)(hx: Slow U (hook x) p)(hy:Slow U (hook y) p)
    (q:Attested m B U (capRow (tailP m B x v) 2 t) (insert 2 (insert 1 {0})))(u:Attested m B U (capRow (tailP m B y v) 2 t) (insert 2 (insert 1 {0})))(M:Tulip.Male):
  hero j l n M m B U x y v= torque j l n M m B U (capRow (arrayZ m B x) 2 t) x (stick 2)-torque j l n M m B U (capRow (arrayZ m B y) 2 t) y (stick 2):=by
  let T (x):=tailP m B x v; let S(x):=capRow (T x) 2 t; let r: Zone:={1,2}; let f:=torque j l n M m B U
  have hc (x) : f (T x) x (stick 1)=f (S x) x (stick 1):=by
    apply equal_ord m B U (T x) (S x) {1} _ x (stick_in 1 (mem_singleton_self _)); rintro ⟨a,i⟩ g; simp only at g; rw [show i=(1:Row) from mem_singleton.mp g]; rfl
  have hb (x): f (capRow (arrayZ m B x) 2 t) x (stick 2)=f (S x) x (stick 2):=by
    apply equal_ord m B U _ _ {2} _ x (stick_in 2 (mem_singleton_self _)); rintro ⟨a,i⟩ g; rw [show i=(2:Row) from mem_singleton.mp g]; rfl
  have he:∀ i:Spot m,i.2∈r→ S x i=S y i:=by rintro ⟨a,i⟩ g; change i∈r at g; fin_cases i <;> first | contradiction|rfl
  change f (T x) x _-f (T y) y _=f _ _ _-f _ _ _; rw [hc,hc,hb,hb]
  exact buks H G hm x y _ _ U M (atop H G hm _ _ q h hx) (atop H G hm _ _ u h hy) he _ _ (stick_in _ (by simp [r])) (stick_in _ (by simp [r]))
lemma soloHero (h:Guard U e)(x y:Sheen m B)(hp:Slow U (hook x) p)(hy:Slow U (hook y) p)(v z:Cue m)(g:tiedC m B U x y v)(lH:tiedC m B U x y z)(M:Tulip.Male): hero j l n M m B U x y v=hero j l n M m B U x y z:=by
  let f:Fin 4→ ArrayF m:= ![tailP m B x v,tailP m B y v,tailP m B x z,tailP m B y z]
  obtain ⟨t,hT⟩:=Att_end m B U (univ: Finset (Fin 4)) f (fun _=>insert 1 {0}) 2 (by simp) (by intro i hi; simp [ending]) (by
    intro i _; fin_cases i; exact g.1; exact g.2; exact lH.1; exact lH.2)
  rw [shared H G hm h v t x y hp hy (hT 0 (by simp)) (hT 1 (by simp)) M,shared H G hm h z t x y hp hy (hT 2 (by simp)) (hT 3 (by simp)) M]
omit H G hm
def lick (j l n:ℕ)(M:Tulip.Male)(m B:Side)(U:Skin m B)(x y:Sheen m B):= hero j l n M m B U x y (gets m B U x y).choose
include H G hm
lemma priceHero(h:Guard U e)(hp:Slow U (hook X) p)(hy:Slow U (hook Y) p)(g:tiedC m B U X Y t)(M:Tulip.Male): lick j l n M m B U X Y=hero j l n M m B U X Y t:= soloHero H G hm h X Y hp hy _ t (gets m B U X Y).choose_spec g M
lemma claim (h:Guard U e)(hp:Slow U (hook X) p)(hy:Slow U (hook Y) p)(M:Tulip.Male): Complex.exp (lick j l n M m B U X Y) • coneP j M U X=coneP j M U Y ∧ coneP j M U X≠0:=by
 obtain ⟨v,q⟩:=gets m B U X Y
 let S:=tailP m B X v; let T:=tailP m B Y v
 obtain ⟨hL,R⟩:=tor_ok H G hm (att_dome q.1 h hp) (stick_in _ (mem_singleton_self 1)) M
 have hT:airing m B U S (stick 1)=airing m B U T (stick 1):=by
   rw [←rise_one _ _ U S (stick 1) X,←rise_one _ _ U T (stick 1) X]; apply ark_same _ _ U S T {1} _ X 1 (stick_in _ (mem_singleton_self 1)); rintro ⟨a,i⟩ g; rw [show i=(1:Row) from mem_singleton.mp g]; rfl
 have hc := (tor_ok H G hm (att_dome q.2 h hy) (stick_in _ (mem_singleton_self 1)) M).1; refine ⟨?_,R⟩
 rw [priceHero H G hm h hp hy q,hero, Complex.exp_sub,div_eq_inv_mul,mul_smul]; unfold antler; rw [hL,hT,←hc,smul_smul, inv_mul_cancel₀ (Complex.exp_ne_zero _),one_smul]
lemma additiveL (h:Guard U e)(hp:Slow U (hook X) p)(hy:Slow U (hook Y) p)(M:Tulip.Male)(Z:Sheen m B)(hz:Slow U (hook Z) p): lick j l n M m B U X Y+lick j l n M m B U Y Z=lick j l n M m B U X Z:=by
 let f:Fin 3→ Sheen m B:= ![X,Y,Z]
 obtain ⟨w,Gz⟩:= tiesT m B U (show ((univ: Finset (Fin 3))).card ≤6 from by simp) f
 have hx: mantle m B U X w:=Gz 0 (mem_univ _); have hu:mantle m B U Y w:=Gz 1 (mem_univ _); have hμ :mantle m B U Z w:=Gz 2 (mem_univ _)
 rw [priceHero H G hm (t:=w) h hp hy ⟨hx,hu⟩,priceHero H G hm (t:=w) h hy hz ⟨hu,hμ⟩,priceHero H G hm (t:=w) h hp hz ⟨hx,hμ⟩]; unfold hero; abel
end YM.CF.Brace
