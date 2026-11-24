import YM.CF.Brace.Capper
set_option autoImplicit false
noncomputable section
namespace YM.CF.Brace
open Function Filter Lattice Metric Lat Finset Cube Tenant SU Fock Dial Phase
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {m B : Side}{U:Skin m B}{s:ArrayF m}{X:Sheen m B}
-- v unnormalized at top, t ramps linearly
def roofV(m B :Side)(U:Skin m B)(s:ArrayF m)(X:Sheen m B)(t:ℝ)(w:Sq):Site (Domain m B)→Vect:=fun i=> t • paint m B U s w i+(1-t) • hook X i
lemma tpiece (l:List ℝ)(s:ℝ): (l.map (s * ·)).sum=s*l.sum:=by induction l with | nil=>simp| cons a l h=>simp [h,mul_add]
lemma atHome {q:Sq}{e p:ℝ}(hq:prob q)(he:0≤e)(g:Guard U e)(hX:Tags s X)(hp:0<p)(hh:Slow U (hook X) p) (r:Zone)(hr:q∈ Phase.zone r)(hR:(0:Row)∉r)(ha:Attested m B U s (insert 0 r))(hn: pot B e*7+7*(4*B.val*p)≤ low/2)(t:ℝ)(h:t∈Set.Icc 0 1)(z:Site (Domain m B)): low/2≤ ‖roofV m B U s X t q z‖:=by
  have ht:0≤t:=h.1; have hc:t≤1:=h.2; have ho:0≤1-t:=sub_nonneg.mpr hc; have he':1-t ≤ 1:= sub_le_self 1 ht
  let S:=bandS m B z q
  obtain ⟨a,l,hl,H,G⟩ := walk_band m B z q hq (subset_refl _) (has_bandS m B z q hq)
  change S=_ at H
  have hv : a∈S := by rw [H]; simp
  have hI i (g:i∈l) : i.1∈S := by rw [H]; simp only [List.mem_toFinset]; exact List.mem_cons_of_mem _ (List.mem_map_of_mem g)
  have hT i (e:i∈S):i.2∈r:=by by_contra v; have g:0<cash m B z q i:=(mem_filter.mp e).2; rw [show cash m B z q i=0 from empty_cash (m:=m) (B:=B) (hr.2 _ v) z i.1] at g; linarith
  let l':=padC m a l
  obtain ⟨hx',hb'⟩:=moves_pad a l hl (fun e=>hR (e ▸ hT a hv)) (fun i g e=>hR (e ▸ hT i.1 (hI i g)))
  have hy: l' ∈fees m a (insert 0 r):=mem_filter.mpr ⟨permits_iff.mpr ⟨hx',free_pad a _ (mem_insert_self ..) l (fun i g=> mem_insert_of_mem (hT i.1 (hI i g)))⟩,hb'⟩
  let b:=coal m (cash m B z q) a l; let L:=serve m B U s a l; let Y:=tray b L
  have hlen : L.length=b.length:= by simp [b,L,coal,menu]
  have hb : b.sum=1 := by
    rw [← cash_sum m B z q hq, ← sum_subset (S.subset_univ), H,List.sum_toFinset _ G]; swap; exact fun i _ hi=>outside hi
    simp [b,coal,List.map_map]; rfl
  have hz : paint m B U s q z = combo (a::l.map Prod.fst) (fun i=>freight m B U z i.1 (s i)) (cash m B z q) := by
    rw [paint,←sum_subset (S.subset_univ),H,List.sum_toFinset _ G]; · rfl
    intro i _ Hx; rw [outside (m:=m) (B:=B) (z:=z) (q:=q) Hx,zero_smul]
  obtain ⟨w,y,W⟩:= handset hX hh hp a l hl; change serve _ _ _ _ _ l'=L++[w] at y
  let b':=(b.map (t * ·))++[1-t]; let V:=serve m B U s a l'; let Z:=tray b' V
  have hlV : V.length≤7:=by unfold V; rw [menu]; have h:=total_len hx'; change l'.length≤6 at h; omega
  have hu:= ha.form hy (mem_insert_of_mem (hT _ hv)); have heB: ∀ i∈b', (0:ℝ)≤ i :=by
    intro i hi; rcases List.mem_append.mp hi with he|he; obtain ⟨j,h,rfl⟩:=List.mem_map.mp he; exact mul_nonneg ht (coal_pos _ _ (cash_nonneg m B z q) _ _ _ h)
    simp only [List.mem_singleton] at he; exact he.symm ▸ ho -- tune
  have hG:= tray_size b' heB V (served m B U s a l') (by rw [show V=L++[w] from y]; simp [b',hlen]) margin_pos hu
  have hQ:Z=t • Y+(1-t) • w:=by unfold Z; rw [show V=L++[w] from y,tray_ext, tray_cash _ _ _ hlen]; simp [hlen]
  have hzB : b'.sum=1:=by unfold b'; rw [List.sum_append,List.sum_cons,List.sum_nil,add_zero]; rw [tpiece]; rw [hb,mul_one]; abel
  have hD: low ≤‖Z‖:=by unfold low; rw [←one_div,div_le_iff₀ (magC_pos _ margin_pos 7),mul_comm]; rw [hzB] at hG; exact hG.trans (mul_le_mul_of_nonneg_right (magC_inc margin margin_pos hlV) (norm_nonneg _))
  let T:=tax m B U z a.1 1; have hd := total_len hl
  have heY : ‖turn T Y-paint m B U s q z‖≤pot B e*7:=by
    rw [hz]; apply (mispaint _ (cash_nonneg m B z q) he g s a l hl (spot_hit hv) (fun i h=> spot_hit (hI i h))).trans; rw [hb,mul_one]
    have H:(l.length:ℝ)≤6 := by exact_mod_cast hd
    exact mul_le_mul_of_nonneg_left (by linarith) (by unfold pot; positivity)
  have heW: ‖turn T w-hook X z‖≤ 7*(4*B.val*p):=by
    let f:= march z (address m B a.1) 1
    have hx:= stroll_h U _ p hh f z; rw [Cube.arrive] at hx -- def
    apply (norm_sub_le_norm_sub_add_norm_sub _ (turn T (hook X (address m B a.1))) _).trans
    rw [← turn_sub, turn_norm]; apply (add_le_add W hx).trans
    have hd':(l.length:ℝ)≤ 6:=by exact_mod_cast hd
    have hl:(f.length:ℝ)≤ 4* B.val := by exact_mod_cast march_len z _ _ (by rw [separation_comm]; exact (node_dist (spot_hit hv)).le)
    nlinarith only [mul_le_mul_of_nonneg_right hd' (show 0≤ (4*B.val*p:ℝ) by positivity),mul_le_mul_of_nonneg_right hl hp.le]
  have hzK : ‖turn T Z-roofV m B U s X t q z‖ ≤ low/2:=by
    rw [roofV,hQ,show ∀ (v w:Vect), turn T (v+w)=turn T v+turn T w from fun i j=>map_add (spinV T) i j,turn_mul,turn_mul,add_sub_add_comm,←smul_sub,← smul_sub]; apply (norm_add_le ..).trans; rw [norm_smul,norm_smul,Real.norm_of_nonneg ht,Real.norm_of_nonneg ho]
    exact (add_le_add ((mul_le_of_le_one_left (norm_nonneg _) hc).trans heY) ((mul_le_of_le_one_left (norm_nonneg _) he').trans heW)).trans hn
  have hb:=norm_le_norm_sub_add (turn T Z) (roofV m B U s X t q z); rw [turn_norm] at hb; linarith
end YM.CF.Brace
