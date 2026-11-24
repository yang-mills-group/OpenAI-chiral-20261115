import YM.CF.Laic.Dune
set_option autoImplicit false
noncomputable section
namespace YM.CF.Laic
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Planned.JetPort Push.Uniform
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m A B L N:Side}{j k:ℕ}{ho:Odd L.val}{d a b:ℝ}{n:ℕ}
variable {e:ℝ}{G:Ratio (CSide m B) (CSide A B)}{T:Roam m A B}{F:Forest T.ratio}{z:Vox m B→ AxisChart group F}{Y:Pricing j L ho (Thread j)}{V:Grasp Y B e}
def CardK(n:Side)(k:ℕ)(J:Toy k n)(b a:ℝ):Prop:= Prints J ∧ handy J ∧ ∀ i,balance a J i ≤ b
abbrev colorX (F:Toy k N):Dress N:= sumU (cavil F)
def reqU(G:Ratio (CSide m B) (CSide A B))(F:Forest T.ratio)(U:Dress (CSide A B))(l m:ℝ)(n:ℕ):Prop:= ReadY F G (fun x=>foot G (U (fine group F x))) l m n
def reqQ(G:Ratio (CSide m B) (CSide A B))(F:Forest T.ratio)(U:Dress (CSide m B))(l m:ℝ)(n:ℕ):Prop:= ReadY F G (fun x=>endorse G (U (outer group F x))) l m n
lemma eris(a b d r s p q:ℝ)(k j n:ℕ)(L:Side)(h:Odd L.val)(P:Spack j L h a b d n)(ha:0<a)(hb:0<b)(hd:0<d)(hr:0<r)(hs:0<s)(hv:0<p)(hu:0<q):∃ A B:ℝ,0<A ∧ 0<B ∧∀ {m N K:Side}{G:Ratio (CSide m K) (CSide N K)}{T:Roam m N K}{F:Forest T.ratio}{z: Vox m K→ AxisChart group F}, Horizon F z k p q → G.count=L → T.ratio=ratio G→ n≤ (CSide m K).val→∀ M:Male,∀ U:Dress (CSide N K),∀ W:Dress (CSide m K),reqU G F U r s k→ reqQ G F W r s k→ relic U→ let f:=emergence L j h G F z M U - flareP L j h M W
 ContDiffAt ℝ ω f 0∧∀ i,entice A (cake k f) i ≤ B :=by
 obtain ⟨c,x,t,y,H⟩:=posta j k n a b d L h P ha hb hd r s hr hs; let Z:=litSpan k p c; let Y:=machinist k (townCost group) q c; let F:=dime k Z ((x+x)*Y); have hZ:0<Z:=litSpan_pos hv t; refine ⟨Z/2,max 1 F,half_pos hZ,lt_max_of_lt_left (by norm_num),?_⟩
 intro m N K G T F z H' g e u M U W w v z'; let X:=emergence L j h G F z M U - flareP L j h M W
 obtain ⟨p,s⟩:= H F e g u M
 let V:= (fun x=> floral L j h G F M U x-partM L j h m K M W (outer group F x))
 have hl: folkM F V c (x+x) k:=(p U w z'.1).opP ((s W v).minus)
 have he(i):X (whisp i)= V (Push.Uniform.curve (station z) i):=by
    let X:= whisp i; let Y:= Push.Uniform.curve (station z) i
    have he: baby F z X= Push.Uniform.fine group F Y:=congrArg Prod.fst ((wellPath i).symm : ears F z X=hats F Y)
    have ht: represent X= Push.Uniform.outer group F Y :=congrArg Prod.snd ((wellPath i).symm : ears F z X=hats F Y)
    change era L j h G M (ears F z X) (U (baby F z X))- partM _ _ _ _ _ _ W (represent X)= _; rw [he,ht,show ears _ _ _= _ from (wellPath i).symm]; rfl
 have hx:= stipulated (escH t hv H' hu.le hl he) hZ; exact ⟨hx.1,fun i=> (hx.2 i).trans (le_max_right ..)⟩
lemma carK (x y: Toy k N)(hx: Prints x)(p:Prints y)(h:handy x)(k:handy y):Prints (x+y) ∧ handy (x+y)∧ colorX (x+y)=colorX x+colorX y ∧ spurTx (x+y)=spurTx x+spurTx y:=by
 have hu(v): cavil (x+y) v=cavil x v+cavil y v:=by
    have he(i j k z):Nacre.halo (x+y) i j k z= Nacre.halo x i j k z+ Nacre.halo y i j k z:=rfl
    ext1 i j; simp only [cavil,Matrix.of_apply, Matrix.add_apply,mold,he, add_mul, sum_add_distrib]
 constructor; · intro i j k v; simp only [Pi.add_apply, smul_add]; rw [hx,p]
 constructor; · intro i j k' C g; change Nacre.halo x _ _ _ _ + Nacre.halo y _ _ _ _= twist _ (Nacre.halo x i j k' C+ Nacre.halo y i j k' C); rw [h,k,map_add]
 constructor
 · funext i; simp only [colorX,sumU,foil,hu,map_add,sum_add_distrib,smul_add, Pi.add_apply]
 funext i; unfold spurTx; have hp(u): pyre (x+y) u=pyre x u+pyre y u:=by ext i j; simp only [pyre,Matrix.of_apply,Pi.add_apply,_root_.add_apply,sum_add_distrib]; rfl
 simp only [hp,map_add,sum_add_distrib,smul_add]; rfl
lemma car_c {X V:Toy k N}{C A:ℝ}(p:CardK N k X C a)(h: CardK N k V A a):CardK N k (X+V) (C+A) a:=by
 obtain ⟨r,s,x⟩:= carK X V p.1 h.1 p.2.1 h.2.1
 refine ⟨r,s,fun i=> le_trans ?_ (add_le_add (p.2.2 i) (h.2.2 i))⟩; unfold balance; rw [← sum_add_distrib]; refine sum_le_sum ?_; intro j _; rw [←sum_add_distrib]; refine sum_le_sum fun s _=>?_ ; simp_rw [Pi.add_apply, ← mul_add]; apply mul_le_mul_of_nonneg_left (norm_add_le ..) (nick_pos _ (notx_zero ..)|>.le)
lemma qmon {X:Toy k N}{A a b c:ℝ}(h:CardK N k X A a)(p:A≤b)(q:c≤a):CardK N k X b c:=by
 refine ⟨h.1,h.2.1,fun i=>(le_trans ?_ (h.2.2 i)).trans p⟩; unfold balance; apply Finset.sum_le_sum fun j _=> Finset.sum_le_sum ?_; intro l t; exact mul_le_mul_of_nonneg_right (nick_rate q (notx_zero ..)) (norm_nonneg _)
lemma repairs {r d' q l:ℝ}(hr:0<r)(hd:0<d')(hk:0<q)(hv:0<l)(v:Spack j L ho a b d n)(ha:0<a)(ht:0<b)(p:0<d)(k:ℕ):∃ A B:ℝ,0<A ∧ 0<B∧∀ {m N K:Side}{G:Ratio (CSide m K) (CSide N K)}{T:Roam m N K}{F:Forest T.ratio}{z:Vox m K→ AxisChart group F}{e:ℝ}{Y:Pricing j L ho (Thread j)}{V:Grasp Y K e}, Hull j L ho a b d e n m N K G T F z Y V→ Horizon F z k q l→∀ M:Male,∀ U:Dress (CSide N K),∀ W:Dress (CSide m K),Ample U→Ample W→ reqU G F U r d' k→ reqQ G F W r d' k→ cFoot k (emergence L j ho G F z M U - flareP L j ho M W)→∃ X:Toy k (CSide m K), CardK (CSide m K) k X B A ∧ Nacre.crystal k (emergence L j ho G F z M U - flareP L j ho M W) (spurTx X):=by
 obtain ⟨A,B,h,H,R⟩:=eris a b d r d' q l k j n L ho v ha ht p hr hd hk hv; obtain ⟨α,K,e,s,D⟩:= posed k A h; refine ⟨α,B*K,e,mul_pos H s,?_⟩; intro m N c G T F z V Y B' w P M U W q l t g hx
 obtain ⟨hr,he⟩:= R P w.fromL w.alignT w.request M U W t g q.self
 have hp:= noct (w.nimbus M q.self q.ripe q.across q.plane) (symmetryP w M l); obtain ⟨C,f,hQ,V,q⟩:=D _ _ (hr.of_le le_top) hp hx B he; refine ⟨_,⟨f,hQ,q⟩,?_⟩; rw [V]; exact (argent (hr.of_le le_top)).mp hx
end YM.CF.Laic
