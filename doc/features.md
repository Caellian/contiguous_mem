<table id="feature-table">
<thead>
    <tr>
        <th><h4>Feature</h4></th>
        <th class="vertical"><h4>Default</h4></th>
        <th><h4>Description</h4></th>
    </tr>
</thead>
<tbody>
    <tr>
        <td><code>std</code></td>
        <td>&check;</td>
        <td>enables <code>std</code> types</td>
    </tr>
    <tr>
        <td><code>unsafe_impl</code></td>
        <td>&check;</td>
        <td>enables <code>UnsafeContiguousMemory</code></td>
    </tr>
    <tr>
        <td><code>debug</code></td>
        <td>&cross;</td>
        <td>enables <code>derive(Debug)</code> on structures unrelated to error handling</td>
    </tr>
</tbody>
<thead>
    <tr class="category nightly">
        <th colspan="3"><h5>Nightly</h5></th>
    </tr>
</thead>
<tbody>
    <tr class="nightly">
        <td><a href="https://doc.rust-lang.org/beta/unstable-book/library-features/ptr-metadata.html"><code>ptr_metadata</code></a></td>
        <td>&cross;</td>
        <td>allows casting references into <code>dyn Trait</code></td>
    </tr>
    <tr class="nightly">
        <td><a href="https://dev-doc.rust-lang.org/stable/unstable-book/library-features/error-in-core.html"><code>error_in_core</code></a></td>
        <td>&cross;</td>
        <td>enables support for <code>core::error::Error</code> in <code>no_std</code> environment</td>
    </tr>
</tbody>
</table>

<style>
#feature-table {
    .vertical {
        vertical-align: bottom;
        text-align: center;
        width: 2.5em;

        >h4 {
            writing-mode: vertical-rl;
            transform: rotate(180deg);
            white-space: nowrap;
            margin: auto;
        }
    }

    .category {
        th {
            padding: .2em;
            padding-left: 1em;
        }

        h5 {
            margin: 0;
            padding: 0;
            text-align: left;
        }

        &.nightly th {
            background: linear-gradient(60deg,  #771749, #1da8ae);
            color: #fffe;
        }
    }

    tr td:nth-child(1) { text-align: center; }
    tr td:nth-child(2) { text-align: center; }
}
</style>
