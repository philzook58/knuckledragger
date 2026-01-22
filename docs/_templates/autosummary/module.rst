{{ fullname | escape | underline}}

.. currentmodule:: {{ fullname }}

.. automodule:: {{ fullname }}
   :members:
   :undoc-members:
   :show-inheritance:
   :member-order: bysource
   :imported-members:

   {% block attributes %}
   {% if attributes %}
   .. rubric:: {{ _('Module Attributes') }}

   {% for item in attributes %}
   .. autodata:: {{ item }}
      :annotation:

   {% endfor %}
   {% endif %}
   {% endblock %}

.. rubric:: Proof Objects

{# Dynamically generate autodata directives for Proof objects #}
{% set modobj = modules[fullname] if fullname in modules else None %}
{% if modobj %}
{%- for name, obj in modobj.__dict__.items() if not name.startswith('_') %}
{%- if obj.__class__.__name__ == 'Proof' %}

.. autodata:: {{ name }}
   :no-value:
{% endif %}
{%- endfor %}
{% endif %}

   {% block functions %}
   {% if functions %}
   .. rubric:: {{ _('Functions') }}

   .. autosummary::
      :toctree:
   {% for item in functions %}
      {{ item }}
   {%- endfor %}
   {% endif %}
   {% endblock %}

   {% block classes %}
   {% if classes %}
   .. rubric:: {{ _('Classes') }}

   .. autosummary::
   {% for item in classes %}
      {{ item }}
   {%- endfor %}
   {% endif %}
   {% endblock %}

   {% block exceptions %}
   {% if exceptions %}
   .. rubric:: {{ _('Exceptions') }}

   .. autosummary::
   {% for item in exceptions %}
      {{ item }}
   {%- endfor %}
   {% endif %}
   {% endblock %}

{% block modules %}
{% if modules %}
.. rubric:: Modules

.. autosummary::
   :toctree:
   :recursive:
{% for item in modules %}
   {{ item }}
{%- endfor %}
{% endif %}
{% endblock %}

.. literalinclude:: ../../{{ fullname | replace(".","/") }}.py
   :language: python