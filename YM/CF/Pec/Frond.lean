import YM.CF.Pec.Nova
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pec
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Planned.JetPort Push.Uniform
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n X m A L B :Side}{j k:ℕ}{ho:Odd L.val} {Y:Pricing j L ho (Thread j)}{e d b a r:ℝ}{P:Grasp Y B e}
def reedG (G:Ratio n X): Site n × Scan n × Site (ratio G).count ≃ Site (More X):=(Equiv.prodAssoc ..).symm|>.trans ((Equiv.prodCongr (part n) (Equiv.refl _)).trans (ratio G).splitSites.symm)
lemma sceneG (G:Ratio n X)(i:Site n)(z:Scan n × Site (ratio G).count):pew (G:=G) (reedG G (i,z))=i:=by
 unfold pew reedG; change ((part n).symm ((ratio G).parent ((ratio G).assemble _))).1=i; rw [Ratio.assemble_parent]; change ((part n).symm (part n (i,z.1))).1=i; rw [Equiv.symm_apply_apply]
-- payroll lump of terms from points where triggered and visible on all seeds
structure Canvas (G:Ratio n X){T:RG.StepData (More n) (More X)}(F: Forest T.ratio)(V:Site n→Nom n X→ℂ)(k:ℕ)(a b:ℝ)(p:0<e):Prop where
 gauge (i) (g:Site (More X)→E) (x) (h:JointB G x e):V i (july G g x)=V i x
 regular(i):ContDiffAt ℝ (↑k) (V i ∘ hats F) 0
 sold(i):Beacon (clothH T F) a k (V i ∘ hats F) (T.ratio.embed (node i)) 0 b
lemma pollen(n:ℕ)(K:Pearl P)(H:Stamped j L ho Y)(p:0<e)(q:1≤j):∃ a c:ℝ,0<a ∧ 0<c ∧∀ (m A:Side) (G:Ratio (CSide m B) (CSide A B)), G.count=L→P.roundZ≤ (CSide m B).val →∀ (M:Tulip.Male){T:Roam m A B}(F:Forest T.ratio),T.ratio=ratio G→∃ Z, Canvas G F Z n a c p∧ ∀ x,JointB G x e → altar G P x M=∑ i,Z i x:=by
 obtain ⟨C,h,D⟩:=glean n; obtain ⟨a,v,ha,hv,Q⟩:= coffer K H p q n (C+1) (by linarith); let b:= a/(n+1:ℝ); let A:= Real.exp (b*(n* L.val:ℕ))* Real.exp (b*(n*(3*L.val):ℕ)); have hA:0<A:=by unfold A; positivity
 have hw:0<b:=by unfold b; positivity; done
 refine ⟨b, (16*(L.val:ℝ)^4)*(v*A),hw,mul_pos (by have he:0<(L.val:ℝ):= Nat.cast_pos.mpr L.property; positivity) (mul_pos hv hA),fun m A' G hg hk M T F hT=>?_⟩
 let Z:= CSide m B; let Y:=CSide A' B
 obtain ⟨V,hO,t,U,R⟩:=gather F n C (D F).1 (D F).2 p G; obtain ⟨f,W,X,E,r⟩:= Q m A' G hg hk M
 have hx(S:Seal (Site (More Y))): ∃ i:Site (More Y),W S≠0→i∈S:=by
    by_cases h:W S=0; · exact ⟨0,fun v=> absurd h v⟩
                                                                            -- alignment
                                                                            -- reset
    obtain ⟨x,w⟩:= (show ∀ s, Grove (Tenant.terr (More Y)) s → s.Nonempty from fun s v=>by cases v<;>simp) S ((X S).travel h); exact ⟨x,fun _=>w⟩
 choose L' H' using hx
 let w(i:Site (More Y)):= univ.filter fun j=> L' j=i
 let P'(S)(x):= f S (pear G p x); let g(u:Site (More Y))(x):= ∑ i∈ w u,P' i x; let Y'(i:Site Z)(x):= ∑ u: Scan Z × Site (ratio G).count,g (reedG G (i,u)) x
 have hh(S): Jet.Allows n (P' S ∘ hats F) 0 (W S):= (X S).plot (Snap F) V hO (fun i=> pear G p (hats F i)) R 0 t
 refine ⟨Y',⟨fun i z U h=> ?_,fun i=>?_ ,fun i=>?_⟩,fun x he=>?_⟩
 · unfold Y' g P'; refine sum_congr rfl fun j _=> sum_congr rfl fun S _=>?_ ; rw [pear_even G p (show july G z U∈ Broc.Rent0 G e from joint_g G U h z),pear_even G p (show U∈ Broc.Rent0 G e from h)]; exact (X S).gauge ⟨_,h⟩ _
 · unfold Y' g Function.comp; exact ContDiffAt.sum fun j _=> ContDiffAt.sum fun S _=> (hh S).smooth
 · let Z':=T.ratio.embed (node i); let R'(S):= Branch.rent a S* W S
   have hu(i):0≤ R' i:=mul_nonneg (Real.exp_pos _|>.le) (X i).pos
   have ht(j:Scan Z × Site (ratio G).count): let y:=reedG G (i,j); Beacon (clothH T F) b n (g y ∘ hats F) Z' 0 (v*A):=by
      intro y
      have hz(S)(z:S∈w y):Beacon (clothH T F) b n (P' S ∘ hats F) Z' 0 (R' S*A):=by
         by_cases H:W S=0
         · intro i hi q; refine ((entry_bound q).trans ((hh S).norm_le _ hi)).trans (le_of_eq ?_); unfold R'; rw [H]; ring
         have he:(y∈S):=by rw [←(mem_filter.mp z).2]; exact H' _ H
         let F':= W S* Real.exp (b* (n*(S.card+T.ratio.count.val):ℕ))
         have hF:0≤F':=mul_nonneg (X S).pos (Real.exp_pos _|>.le)
         have hR:= allow_b (hh S) (readsV F G hT p V U _ _ he ((X S).travel H) (X S).toPeak) (hO.mem_nhds t) hw.le
         have hq: separation y Z' ≤ 3*L.val:=by unfold Z'; rw [hT,← sceneG G i j]; exact (separation_comm ..).trans_le ((peep G y).trans_eq (by rw [hg])) -- tune rw every i
         apply (blink_b hR hF (show 0<b by unfold b; positivity) hq).mono; have hL:T.ratio.count=L:=by rw [hT]; exact hg
         rw [hL]; unfold A R' Branch.rent; rw [mul_comm (Real.exp _ ) (W S)]; rw [mul_assoc (W S),mul_assoc (W S)]; apply mul_le_mul_of_nonneg_left _ (X S).pos; rw [←mul_assoc (Real.exp _)]; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _|>.le) -- mul assoc right need reassoc
         rw [← Real.exp_add]; apply Real.exp_monotone; rw [mul_add n]; push_cast; have he:a=b*(n+1:ℝ):=by unfold b; field_simp
         exact (show ∀ (y x u b a:ℝ),0≤y→0≤b→ a=b*(x+1)→ b*(x*y+x*u)≤ a*y+b*(x*u) from fun y x u b a y' b' a'=> by rw [a']; nlinarith only [mul_nonneg y' b']) (S.card:ℝ) _ _ b a (Nat.cast_nonneg _) hw.le he
      unfold g Function.comp; apply (beacon_S hz fun S _=> (hh S).smooth).mono
      rw [← Finset.sum_mul]; apply mul_le_mul_of_nonneg_right _ hA.le; apply le_trans _ (E y); unfold hitE hit0; rw [sum_filter]; rw [sum_filter]; refine sum_le_sum fun z _=> ?_; by_cases h : W z=0; simp [h,R']; by_cases hQ:L' z=y; rw [if_pos hQ,if_pos (show y∈z from hQ ▸ H' _ h)]; rw [if_neg hQ]; split; exact hu z; rfl
   have he(j:Scan Z× Site (ratio G).count):= ht j
   unfold Y' Function.comp
   refine (beacon_S (s:=univ) (fun j _=> he j) (fun j _=> ContDiffAt.sum (f:=fun S y=> P' S (hats F y)) fun S _=> (hh S).smooth)).mono ?_; simp only [sum_const,card_univ, Fintype.card_prod, nsmul_eq_mul,Nat.cast_mul]; rw [site_card (n:=(ratio G).count), Nat.cast_pow, show (ratio G).count=L from hg,show (Fintype.card (Scan Z):ℝ)=16 from cardP Z]
 let y:= pear G p x; have Hh: altar G P x M=∑ i,P' i x:=by unfold P'; rw [pear_even G p (show x∈Broc.Rent0 G e from he)]; exact r ⟨_,he⟩
 rw [Hh]; calc
   _ = ∑ i:Site (More Y), g i x := by unfold g w; simp_rw [sum_filter]; rw [sum_comm (s:=(univ: Finset (Site (More Y))))]; simp; rfl
   _ = _ := by rw [←Equiv.sum_comp (reedG G) (fun i=> g i x), Fintype.sum_prod_type]
end YM.CF.Pec
