import YM.CF.Pec.Realm
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pec
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n:Side}{δ:ℝ}
abbrev Scan(n:Side):= Site (assembly n).count
def poolY (i:Site n)(j:Scan n):Orig n:= (assembly n).assemble (i,j)+1
def part(n:Side): Site n × Scan n ≃ Orig n:=((assembly n).splitSites.symm).trans (Equiv.addRight 1) -- inspect
lemma dealU(i:Site n)(s:Scan n): separation (node i) (poolY i s)≤ 2:=by
 unfold node poolY; rw [separation_translate,Ratio.root_embed]; let g:=assembly n; let X:= g.assemble (i,s); have ht:= Corona.near g X; rw [show g.parent X=i from g.assemble_parent _] at ht; exact (separation_comm ..).trans_le (show separation X (g.embed i) ≤ 2 from (by change 2* _≤ 2 at ht; omega))
abbrev RegHour:=Bool × Bool
def pore(x:Site n)(p:PlaqAxes)(i:RegHour):Site n:=x-(if i.1 then step p.val.1 else 0)-(if i.2 then step p.val.2 else 0)
lemma poreC(x:Orig n)(p:PlaqAxes)(v:RegHour):separation x (pore x p v)≤2:=by
 have he(a:Orig n)(b:Axis)(v:Bool): separation a (a-(if v then step b else 0)) ≤1:=by cases v; simp; exact (by simp [separation]; exact pdist_step b)
 exact (separation_triangle x (x- _) _).trans (Nat.add_le_add (he x p.val.1 v.1) (he (x-_) p.val.2 v.2))
def cardw(n:Side):ℝ:=↑(Fintype.card (Scan n))
lemma cardP(n:Side):cardw n=16:=by rw [cardw, site_card]; norm_num [assembly]
abbrev Tonic (n:Side):= PlaqAxes × PlaqAxes × Scan n × RegHour × RegHour
def atV(x:Site n)(t:Tonic n):Ok n×Ok n:=
 let y:=poolY x t.2.2.1; let p:=t.1; let q:=t.2.1
 (Sum.inl (pore y p t.2.2.2.1,p),Sum.inl (pore y q t.2.2.2.2,q))
def valueV(P:Case)(p q:PlaqAxes):=(256:ℝ)⁻¹ • P p q
def roan(P:Case):Pride n:= fun i j k=>∑ l:Tonic n, if atV i l=(j,k) then valueV P l.1 l.2.1 else 0
lemma roan_m(P:Case)(x:Site n):mom (roan P x)=P:=by
 funext i j; unfold mom; simp_rw [roan]; rw [show ∀(f: Orig n→ Orig n→ Tonic n→ℂ), ∑ i:Orig n,∑ j,∑ k,f i j k=∑ k,∑ i,∑ j,f i j k from fun f=>by rw [sum_comm (s:=(univ:Finset (Tonic n)))]; apply sum_congr rfl; intro; intro; rw [sum_comm]]
 unfold Tonic; rw [Fintype.sum_prod_type]; rw [Finset.sum_eq_single i]; swap; intro y _ hy; simp [atV,hy,poolY]; swap; simp
 rw [Fintype.sum_prod_type, sum_eq_single j]; swap; intro y _ hy; simp [atV,hy,poolY]; swap; simp
 have hh(k:Orig n)(l:Orig n):∑ v:Orig n,∑ w: Orig n,(if k=v∧ l=w then valueV P i j else 0) =valueV P i j:=by rw [Finset.sum_eq_single k]; simp; intro x _ hx; simp [Ne.symm hx]; simp
 have he:Fintype.card (Scan n)=16:=by exact_mod_cast (show (Fintype.card (Scan n):ℝ)=16 from cardP n)
 rw [Fintype.sum_prod_type]; simp_rw [atV]; simp only [Prod.mk.injEq,Sum.inl.injEq,and_true,true_and]; simp_rw [hh]; simp only [sum_const,card_univ, he]; rw [show Fintype.card (RegHour × RegHour)=16 by decide]; simp [valueV]; ring
lemma rosemary (x a: Site n)(v:Scan n): poolY (x+a) v = poolY x v + (assembly n).embed a:=by unfold poolY Ratio.assemble; rw [← Ratio.root_embed,map_add,Ratio.root_embed]; simp only [Ratio.root_embed]; abel
lemma roan_t(P:Case): WordK (n:=n) (roan P):=by
 intro i t a b; unfold roan; refine sum_congr rfl ?_; intro k _; have he : atV (i+t) k=((feedback t) ((atV i k).1), feedback t ((atV i k).2)):=by
    have hp(v:Scan n)(q:PlaqAxes)(d:RegHour): Sum.inl (pore (poolY (i+t) v) q d,q)=feedback t (Sum.inl (pore (poolY i v) q d,q)):=by
       unfold feedback; apply Eq.symm; let E:= pore (poolY i v) q d; change Sum.inl (E+wrap _ (2 • lift t),q)= Sum.inl (pore _ _ _,q); apply congrArg (fun x:Orig n=>Sum.inl (x,q)); -- tune implicit
       rw [show wrap (More n) (2 • lift t)=(assembly n).embed t from by rw [← show (assembly n).embed (wrap n (lift t))= wrap _ (2 • lift t) from Ratio.embed_wrap ..,wrap_lift]]; unfold E pore; rw [rosemary]; abel
    exact Prod.ext (hp _ _ _) (hp _ _ _)
 rw [he]; cases (atV i k); simp
end YM.CF.Pec
