import YM.SU5.Relativistic.Fanfare
/-!
# Arrays of copies in one direction: power stack for pre-election rt

Alignment lemma via native wraps and natural planes per copy. Keeps width
linear in length * width. Product still ordered multiplicatively in character.
Prove `StageTw` closure separately already. 
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.ScreeV
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Lifted Afterglow Tapestry Branch Tenant Skye Cliplet RG Brace Crest Crest.Sleet Crest.Sleet.UpStart Satin Tower.SlabMark
open Afterglow.Tower (reflectedBox)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {k j w d l u T H:ℕ}{R γ τ γ' B E:ℝ}{K: Calibration}{M:Tulip.Male}
variable {n:Side}{z:Axis}{i:ℕ}{N:Side}

-- pre perturb. Tower with width on cover; Pack. keep dependencies fixed for all m by upper HT statement.
structure Batch (K:Calibration)(F:Buffered.Family K)(T:Finset Cover)(q:ℕ)(m:Side)(j:ℕ)(M:Tulip.Male)(k w d l u:ℕ)(γ γ' τ E R:ℝ): Prop where
 ticket:∃ L:List (Cliplet (K.c m) k), L.length=q ∧ whereV L⊆ Satin.region T (K.c m) ∧ probe L= F m∧Company j M w d l u γ γ' τ E R L
variable {F Y:Buffered.Family K}{S S':Finset Cover}{q q':ℕ}
namespace Batch
variable {X : Mark (K.c n)→ℂ}
local notation "U" F:max s:max x:max=> Batch K F s x n j M k w d l u γ γ' τ E R
lemma inverted (h:U F S q)(i:Axis)(s:ℤ)(b:∀ z,twist (carR i s (K.c n)) (sp z j M (1:Pane (K.c n)))=sp (!z) j M (1:Pane (K.c n))): U (Tower.mirror K i s F) (reflectedBox i s S) q:=by
 obtain ⟨L,t,p,v,f⟩:= h.ticket
 refine ⟨L.map (fun a=>a.mirror i s),by rw [List.length_map,t],?_, by rw [Flight.reflect_probes,v]; rfl, f.cloud _ _ b⟩
 rw [Flight.reflect_consistent]; intro z t; obtain ⟨a,u,rfl⟩:= mem_image.mp t; obtain ⟨x,u',rfl⟩:=mem_image.mp (p u); rw [Shape.anno]; exact mem_image_of_mem _ (mem_image_of_mem ((plane i s).motion) u')
lemma migrate (h:U F S q)(i:Axis)(s:ℤ)(b:∀ (s:ℤ) z,twist (carR i s (K.c n)) (sp z j M (1:Pane (K.c n)))=sp (!z) j M (1:Pane (K.c n))): U (relocate K i s F) (plow K i s S) q:= by
 have hp:= (h.inverted i 0 (b _)).inverted i (gaugeT K s) (b _); rw [Tower.support_translation,sub_zero] at hp; exact hp

lemma line (p:U F S q)(v:U Y S' q') (d:Disjoint (region S (K.c n)) (region S' (K.c n))):U (F*Y) (S∪S') (q+q'):=by
 obtain ⟨A,t,h,z,f⟩:=p.ticket; obtain ⟨L,g,x,y,w⟩:=v.ticket; refine ⟨A++L,by rw [List.length_append,t,g],?_,by rw [probe_combine,z,y]; rfl, f.tack L w (d.mono h x)⟩
 rw [combine,Satin.region,image_union]; exact union_subset_union h x
lemma disjoint_later (e:Disjoint S S'): ∃ B:ℕ,∀ n:Side,B≤ n.val→ Disjoint (region S n) (region S' n):=by
 obtain ⟨B,v⟩:= disperse_wrap (S ∪ S'); refine ⟨B,fun n p=>?_⟩; apply Finset.disjoint_left.mpr; intro a h g; obtain ⟨x,htp,rfl⟩:=mem_image.mp h; obtain ⟨y,hx,hg⟩:=mem_image.mp g; have he:y=x:= v (More n) (show _ from p.trans (show n.val ≤ n.val*2 by omega)) (show y∈ (↑(S∪ S') : Set _) from mem_union_right _ hx) (show x∈ (↑(S∪ S'):Set _) from mem_union_left _ htp) hg; exact disjoint_left.mp e htp (he ▸ hx) -- duplicate h

end Batch

abbrev CFam (K :Calibration):=Buffered.Family K
-- use right-normal stack (orientation block first)
def tripleWide (K:Calibration)(z:Axis)(s:ℕ)(f:CFam K):CFam K:= Tower.mirror K z (gaugeT K s) f* relocate K z s f
def thicket (K:Calibration)(z:Axis)(s:ℕ)(f:CFam K):ℕ→ CFam K
| 0=> tripleWide K z s f
| n+1=> tripleWide K z s f * relocate K z (s+s:ℕ) (thicket K z s f n)
-- length=#unprojected marks
abbrev staveP(q:ℕ):=2*(q+1)
abbrev towerH (u q:ℕ):=staveP q*u
namespace Thicket
local notation "θ"=>K.ℓ
local notation "V"=> ruler K.B
variable {z:Axis}

private lemma ladder (p:0< H)(B₀:Cover)(g:Between K z 0 (V*H) S)(u:Transom z S B₀ q): let A:=reflectedBox z (gaugeT K H) S; let T:=plow K z ↑H S
   Disjoint A T ∧ Between K z 0 (V*(H+H:ℕ)) (A∪T)∧Transom z (A∪T) B₀ q:=by
 intro A S'; let h:=V*H
 have hp:Between K z 0 h A:=by have he:= g.mirror K z (gaugeT K H); rw [ruler_offset,sub_zero,sub_self] at he; exact he
 have ht:Between K z h (V*(H+H:ℕ)) S':=by have ht:= g.relocate K z H; rw [add_zero] at ht; unfold h; push_cast; rw [mul_add]; exact ht
 have hf:0≤h:=by unfold h; have ht:=ruler_gene K.B; positivity
 refine ⟨?_,fun i v=> ?_,fun i t x w=>?_⟩
 · apply Finset.disjoint_left.mpr; intro i v w; have he: 0<K.ℓ:=(Nat.zero_le _).trans_lt K.buffer; have hx:=(hp i v).2; have hy:=(ht i w).1; omega
 · rcases mem_union.mp v with v|v
   · obtain ⟨a,e⟩:=hp i v; exact ⟨a,e.trans (by push_cast; rw [mul_add]; omega)⟩
   obtain ⟨a,e⟩:=ht i v; exact ⟨by omega,e⟩
 exact (mem_union.mp w).elim ((u.mirro z _) i t _) ((u.moved K z _) i t _)

-- proofs independent of w etc for support/timing: keep evidence for ANY stage with this starter
lemma express {s:ℕ}(p:0<s)(U:Between K z 0 (V*s) S)(x:Cover)(u':Transom z S x q)(v:InTest K true S false F)(N₀:ℕ):∃ (T:Finset Cover)(B:ℕ), Between K z 0 (V*(towerH s N₀:ℕ)) T ∧ Transom z T x q ∧
        InTest K true T false (thicket K z s F N₀) ∧
   ∀ n:Side,B≤ (K.c n).val→∀ j k w d l u:ℕ,∀ (M:Tulip.Male)(γ γ' τ E R R':ℝ),∀ PrB:Mark (K.c n)→ℂ,StageTw K PrB j R d M → Batch K F S 1 n j M k w d l u γ γ' τ E R' → Batch K (thicket K z s F N₀) T (staveP N₀) n j M k w d l u γ γ' τ E R':=by
 obtain ⟨e,y,H⟩:= ladder p x U u'; let S1:=reflectedBox z (gaugeT K s) S; let S2:= plow K z s S; let Z:= S1∪ S2; let P(s:ℕ):=V*s; let F':=tripleWide K z s F
 obtain ⟨B,f⟩:=Batch.disjoint_later e
 have hp(n:Side)(p:B≤(K.c n).val)(j k w d l u:ℕ)(M:Tulip.Male)(γ γ' τ E R R':ℝ)(PrB:Mark (K.c n)→ℂ)(b:StageTw K PrB j R d M)(t:Batch K F S 1 n j M k w d l u γ γ' τ E R'):
     Batch K F' Z 2 n j M k w d l u γ γ' τ E R':= (t.inverted _ _ (b.across z _)).line (t.migrate _ s (b.across z)) (f _ p)
 have hu:InTest K true Z false F':= ((Tower.axial K z (gaugeT K s) v).mono subset_union_left).mul ((Tower.flow_port K z (gaugeT K s) v).mono subset_union_right)
 have hy:Between K z 0 (P (s+s)) Z:=y; have hQ:Transom z Z x q:=H
 induction N₀ with
 | zero=>
    have he:towerH s 0=s+s:=by unfold towerH staveP; omega
    exact ⟨Z,B,by rw [he]; exact hy,hQ,hu,hp⟩
 | succ n ih=>
    obtain ⟨T,F₀,l0,l1,v,t⟩:= ih
    let q':= P (s+s); let T':=plow K z (s+s:ℕ) T; have hR:P (towerH s (n+1))=q'+V*(towerH s n:ℕ):=by unfold q' P towerH staveP; push_cast; ring
    have he:Between K z q' (P (towerH s (n+1))) T':=by rw [hR]; have hx:= l0.relocate K z ↑(s+s); rw [add_zero] at hx; exact hx
    have hx: Disjoint Z T':= by
       apply Finset.disjoint_left.mpr; intro i v w; have h:=(he i w).1; have u:=(hy i v).2; change _ ≤ q' at u; have hp: 0<K.ℓ:=(Nat.zero_le _).trans_lt K.buffer; omega
    let qT:= P (towerH s (n+1)); have hr:P (s+s) ≤ qT:=by
       have ht:0≤ V*(towerH s n:ℕ):=by have he:=ruler_gene K.B; positivity
       change q'≤ qT; unfold qT; rw [hR]; omega
    let A:=Z∪T'
    obtain ⟨W,g⟩:=Batch.disjoint_later hx; refine ⟨A,W+B+F₀,fun i w=>?_,fun j x t p=>?_,(hu.mono subset_union_left).mul ((Tower.flow_port K z _ v).mono subset_union_right),fun i e j k w d l u M γ γ' τ E R R' PrB b g'=>?_⟩
    · rcases mem_union.mp w with v|v
      · exact ⟨(hy i v).1, (hy i v).2.trans hr⟩
      obtain ⟨h,e⟩:=he i v; refine ⟨?_,e⟩; have hx: 0≤q':= by unfold q' P; have ht:=ruler_gene K.B; positivity
      omega
    · exact (mem_union.mp p).elim (hQ _ x t) ((l1.moved K z _) _ x t)
    have h:=t i (by omega) j k w d l u M γ γ' τ E R R' PrB b g'; rw [show staveP (n+1)=2+staveP n from by unfold staveP; omega]; exact (hp i (by omega) _ _ _ _ _ _ _ _ _ _ _ _ _ _ b g').line (h.migrate z _ (b.across z)) (g _ (by omega))
end Thicket
end YM.CF.Pannier.Chancel.ScreeV
#print axioms YM.CF.Pannier.Chancel.ScreeV.Thicket.express
