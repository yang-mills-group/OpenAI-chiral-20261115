import YM.CF.Rel.Caps
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
open Stationary Push.Loops
open Cube
abbrev Charm:= Site 2
def gammaT (n:Side) (d:Charm):Site (More n):= wrap (More n) (n.val • Lattice.lift d)
-- Θ moment actual
def phi (d:Charm):Axis→ℝ:=fun i=> (mon d i).re
lemma fitP(n:Side)(d:Charm): Push.Loops.Matches (axes (phi d)) (gammaT n d):=by
 refine ⟨_,?_,rfl⟩; funext i; have he : axes (phi d)=mon d:= by ext1 i; apply Complex.ext; simp [axes,phi]; have hp:= real_frequency d; have ht:=congr_arg Complex.im (congr_fun hp i); simp only [Pi.star_apply, Complex.star_def,Complex.conj_im] at ht; unfold axes; rw [Complex.ofReal_im]; linarith
 rw [he]; unfold mon quant; change (2:ℂ)⁻¹*_=_; -- tune
 simp only [reciprocal,Pi.smul_apply,smul_eq_mul,nsmul_eq_mul,Int.cast_mul,Int.cast_natCast, More, PNat.mul_coe,Nat.cast_mul]; field_simp [side_ne]; change _*((2:ℕ):ℂ)=2*(( (n.val:ℤ) * lift d i:ℤ):ℂ); push_cast; ring
lemma gamma_pay(n:Side)(x: Site (More n))(d:Charm): cell (gammaT n d) x=cell d ((assembly n).residue x):=by
 nth_rw 1 2 [← wrap_lift x]; rw [Ratio.residue_wrap,←(fitP n d).read]; change _=cell d (wrap 2 _); rw [cell_wrap]; congr 1; funext i; have he:=congr_fun (real_frequency d) i; simp only [Pi.star_apply,Complex.star_def] at he; apply Complex.ext; rfl; unfold axes; rw [Complex.ofReal_im]; have hp:= congr_arg Complex.im he; rw [Complex.conj_im] at hp; linarith
abbrev logo (n:Side)(c: Charm): Site (More n):=wrap _ (Lattice.lift c)
lemma mount (n:Side)(k i:Charm): cell (gammaT n k) (logo n i)= cell k i:=by rw [gamma_pay,logo,Ratio.residue_wrap]; change cell k (wrap 2 (Lattice.lift i))= _; rw [wrap_lift]
lemma code_m (n:Side)(k:Charm)(i:Site n):pulseP (gammaT n k) ((assembly n).embed i)=1:=by unfold pulseP; rw [gamma_pay,Ratio.residue_embed]; change (cell k 0)⁻¹=1; rw [cell_origin,inv_one]
-- periodicity F
variable {k x:Site (More n)}{F:FileM (More n) G}
def LayerP (n:Side)(F:FileM (More n) G):Prop:=∀ x:Site (More n),∀ y:Site n, F (x+(assembly n).embed y)=F x∘ Lattice.translate ((assembly n).embed y)
-- projection centered average
abbrev massX:ℂ:= Fintype.card Charm
def reel (d:Charm)(n:Side)(F:FileM (More n) G): SpaceX G (More n):= massX⁻¹ • ∑ i: Charm, cell d i • (F (logo n i) ∘ Lattice.translate (-logo n i))
def laidC (d:Charm)(n:Side)(F:FileM (More n) G):FileM (More n) G:= Sean (gammaT n d) (reel d n F)
lemma revive(d:Charm)(n:Side)(F:FileM (More n) G):shapeV (gammaT n d) (laidC d n F):=Sea _ _
lemma summit(n: Side)(k:Charm)(F:FileM (More n) G): LayerP n (laidC k n F):=by
 intro x y; let b:= (assembly n).embed y; let f:= reel k n F; ext1 V; change pulseP (gammaT n k) (x+b)* f _= pulseP _ x*f _; rw [pulse_l, code_m,mul_one]; congr 1; apply congr_arg f; funext p; unfold Lattice.translate; congr 2; exact (add_assoc (p.1:Site (More n)) x b).symm
lemma born(k:Charm)(F:FileM (More n) G)(i:Charm)(v:Config G (More n)): laidC k n F (logo n i) v= pulseP (gammaT n k) (logo n i)* (massX⁻¹*∑ d:Charm,cell k d*F (logo n d) (Lattice.translate (-logo n d + logo n i) v)):=by
 change pulseP _ _* reel k n F _= _; unfold reel; simp only [Pi.smul_apply,Finset.sum_apply,Function.comp_apply,smul_eq_mul]; congr 2; apply sum_congr rfl; intro d _; rw [show Lattice.translate (-logo n d) (Lattice.translate (logo n i) v)= _ from ?_]; ext1 p; unfold Lattice.translate; congr 2; apply add_assoc
lemma mass_p: massX ≠0:=Nat.cast_ne_zero.mpr Fintype.card_ne_zero
lemma ssum (n:Side)(F:FileM (More n) G)(p:LayerP n F): ∑ d:Charm,laidC d n F=F:=by
 ext1 x; obtain ⟨⟨y,z⟩,rfl⟩:= (assembly n).assemble_bijective.2 x; change Charm at z
 let X:=logo n z; let a:=(assembly n).embed y; rw [show (assembly n).assemble (y,z)=X+a from add_comm ..,Finset.sum_apply]; rw [p X y]; simp_rw [show ∀ d:Charm, laidC d n F (X+a)=laidC d n F X∘ Lattice.translate a from fun d=> summit n d F X y]; ext1 v; rw [Finset.sum_apply]; change (∑ d,laidC d n F X (Lattice.translate a v))= F X _; simp_rw [X,born,pulseP,mount,mul_left_comm _ massX⁻¹,mul_sum]; rw [sum_comm];
 let V(i:Charm):=F (logo n i) (Lattice.translate (-logo n i+logo n z) (Lattice.translate a v)); change ∑ i,∑ d,massX⁻¹ *((cell d z)⁻¹*(cell d i*V i))= _; simp_rw [←mul_sum, show ∀ d i,(cell d z)⁻¹*(cell d i *V i)=(cell d i*(cell d z)⁻¹)*V i from fun d i=>by ring,←sum_mul]; simp_rw [cell_duality _ (z:Charm)]
 have he (i:Charm) : (∑ d: Charm, cell d i * (cell z d)⁻¹)= if i=z then massX else 0:=by simp_rw [cell_duality (_:Charm) i]; rw [orthogonal]; split <;> first | norm_num [massX,Charm]|rfl -- tune
 simp_rw [he]; simp only [ite_mul,zero_mul,sum_ite_eq',mem_univ,↓reduceIte,←mul_assoc,inv_mul_cancel₀ mass_p,one_mul]; unfold V; rw [neg_add_cancel]; congr 1; ext1 p; simp [Lattice.translate,a]
end YM.CF.Rel
